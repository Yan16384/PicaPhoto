package com.picaphoto.app;

import android.Manifest;
import android.app.Activity;
import android.app.PendingIntent;
import android.content.ContentUris;
import android.content.ContentValues;
import android.content.Context;
import android.content.Intent;
import android.content.IntentSender;
import android.content.pm.PackageManager;
import android.database.Cursor;
import android.graphics.Bitmap;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.util.Size;
import android.provider.MediaStore;
import android.view.View;
import android.webkit.JavascriptInterface;
import android.webkit.WebResourceResponse;
import android.webkit.WebView;
import android.app.DownloadManager;
import android.content.BroadcastReceiver;
import android.content.IntentFilter;
import android.provider.Settings;
import android.widget.Toast;

import androidx.core.content.FileProvider;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Collections;
import java.util.Arrays;
import java.security.MessageDigest;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicInteger;

public class MediaBridge {
    private final Activity activity;
    private final ExecutorService io = Executors.newFixedThreadPool(3);
    private final File thumbDir;
    private final AtomicInteger thumbWrites = new AtomicInteger(0);
    private static final long THUMB_MAX_BYTES = 96L * 1024L * 1024L;
    private static final long THUMB_TARGET_BYTES = 72L * 1024L * 1024L;
    private static final int THUMB_MAX_FILES = 3000;
    private WebView web = null;
    private Runnable appReadyCallback = null;
    public static final int REQ_PERM = 2001;

    public static final int DELETE_REQ = 2002;
    public static final int WRITE_REQ = 2003;
    public static final int WRITE_BATCH_REQ = 2004;
    public static final int MANAGE_MEDIA_PREP_REQ = 2005;
    private long pendingId = -1;
    private List<Uri> pendingDeleteUris = new ArrayList<>();
    private File lastApk = null;
    private BroadcastReceiver receiver = null;
    private PendingMove pendingMove = null;
    private String pendingWriteBatchCallback = null;

    private static final class PendingMove {
        final String jsonUris;
        final String relativePath;
        final String callback;
        final String firstResults;
        PendingMove(String jsonUris, String relativePath, String callback, String firstResults) {
            this.jsonUris = jsonUris;
            this.relativePath = relativePath;
            this.callback = callback;
            this.firstResults = firstResults;
        }
    }

    public MediaBridge(Activity a) {
        activity = a;
        thumbDir = new File(a.getCacheDir(), "thumbs_v3");
        try { if (!thumbDir.exists()) thumbDir.mkdirs(); } catch (Exception ignored) {}
        try { io.execute(this::cleanupThumbCache); } catch (Exception ignored) {}
    }

    /* 由 MainActivity 注入 WebView，用于后台线程完成后回调 JS */
    public void attachWeb(WebView w) { this.web = w; }
    public void setAppReadyCallback(Runnable r) { this.appReadyCallback = r; }

    @JavascriptInterface
    public void appReady() {
        activity.runOnUiThread(() -> {
            if (appReadyCallback != null) appReadyCallback.run();
        });
    }

    public void destroy() {
        try { io.shutdownNow(); } catch (Exception ignored) {}
        try {
            if (receiver != null) {
                activity.unregisterReceiver(receiver);
                receiver = null;
            }
        } catch (Exception ignored) {}
        web = null;
        appReadyCallback = null;
        pendingMove = null;
    }

    private boolean isVideo(Uri u) {
        String m = activity.getContentResolver().getType(u);
        return m != null && m.startsWith("video/");
    }

    /* 后台线程执行完成后回调 JS（避免大相册查询/文件复制阻塞 WebView 主线程） */
    private void callJs(final String fn, final String json) {
        if (fn == null || !fn.matches("[A-Za-z0-9_$]+")) return;
        activity.runOnUiThread(() -> {
            if (web != null) {
                web.evaluateJavascript("window." + fn + " && window." + fn + "('" + escapeJs(json) + "')", null);
            }
        });
    }

    private String escapeJs(String s) {
        if (s == null) return "";
        return s.replace("\\", "\\\\")
                .replace("'", "\\'")
                .replace("\n", "\\n")
                .replace("\r", "\\r")
                .replace("\u2028", "\\u2028")
                .replace("\u2029", "\\u2029");
    }

    @JavascriptInterface
    public boolean hasImagePermission() {
        if (Build.VERSION.SDK_INT < 23) return true;
        if (Build.VERSION.SDK_INT >= 33) {
            return activity.checkSelfPermission(Manifest.permission.READ_MEDIA_IMAGES) == PackageManager.PERMISSION_GRANTED;
        }
        return activity.checkSelfPermission(Manifest.permission.READ_EXTERNAL_STORAGE) == PackageManager.PERMISSION_GRANTED;
    }

    @JavascriptInterface
    public boolean hasVideoPermission() {
        if (Build.VERSION.SDK_INT < 23) return true;
        if (Build.VERSION.SDK_INT >= 33) {
            return activity.checkSelfPermission(Manifest.permission.READ_MEDIA_VIDEO) == PackageManager.PERMISSION_GRANTED;
        }
        return activity.checkSelfPermission(Manifest.permission.READ_EXTERNAL_STORAGE) == PackageManager.PERMISSION_GRANTED;
    }

    @JavascriptInterface
    public boolean hasPermission() {
        return hasImagePermission() || hasVideoPermission();
    }

    @JavascriptInterface
    public void requestPermission() {
        if (Build.VERSION.SDK_INT < 23) return;
        activity.runOnUiThread(() -> {
            if (Build.VERSION.SDK_INT >= 33) {
                activity.requestPermissions(new String[]{Manifest.permission.READ_MEDIA_IMAGES, Manifest.permission.READ_MEDIA_VIDEO,
                        Manifest.permission.ACCESS_MEDIA_LOCATION}, REQ_PERM);
            } else {
                activity.requestPermissions(new String[]{Manifest.permission.READ_EXTERNAL_STORAGE,
                        Manifest.permission.ACCESS_MEDIA_LOCATION}, REQ_PERM);
            }
        });
    }

    @JavascriptInterface
    public boolean supportsManageMedia() {
        if (Build.VERSION.SDK_INT < 31) return false;
        Intent intent = new Intent(Settings.ACTION_REQUEST_MANAGE_MEDIA,
                Uri.parse("package:" + activity.getPackageName()));
        return intent.resolveActivity(activity.getPackageManager()) != null;
    }

    @JavascriptInterface
    public boolean canManageMedia() {
        return Build.VERSION.SDK_INT >= 31 && MediaStore.canManageMedia(activity);
    }

    @JavascriptInterface
    public void requestManageMedia() {
        if (Build.VERSION.SDK_INT < 31) return;
        activity.runOnUiThread(() -> {
            if (activity.checkSelfPermission(Manifest.permission.ACCESS_MEDIA_LOCATION) != PackageManager.PERMISSION_GRANTED) {
                activity.requestPermissions(new String[]{Manifest.permission.ACCESS_MEDIA_LOCATION}, MANAGE_MEDIA_PREP_REQ);
                return;
            }
            launchManageMediaSettings();
        });
    }

    public void onPermissionResult(int requestCode) {
        if (requestCode == MANAGE_MEDIA_PREP_REQ) {
            if (activity.checkSelfPermission(Manifest.permission.ACCESS_MEDIA_LOCATION) == PackageManager.PERMISSION_GRANTED) {
                launchManageMediaSettings();
            } else {
                toast("需要允许相册位置信息访问，才能免除重复确认");
            }
        }
    }

    private void launchManageMediaSettings() {
        if (Build.VERSION.SDK_INT < 31) return;
        activity.runOnUiThread(() -> {
            try {
                Intent intent = new Intent(Settings.ACTION_REQUEST_MANAGE_MEDIA,
                        Uri.parse("package:" + activity.getPackageName()));
                activity.startActivity(intent);
            } catch (Exception e) {
                toast("此系统未提供相册管理特殊访问");
            }
        });
    }

    @JavascriptInterface
    public void requestWriteBatch(final String jsonUris, final String cb) {
        if (Build.VERSION.SDK_INT < 30) { callJs(cb, "true"); return; }
        /* MANAGE_MEDIA is broader than per-URI grants. checkUriPermission() may still
           report DENIED on vendor ROMs (including vivo/iQOO), so do not open a
           redundant createWriteRequest dialog after special access is enabled. */
        if (Build.VERSION.SDK_INT >= 31 && MediaStore.canManageMedia(activity)) {
            callJs(cb, "true");
            return;
        }
        io.execute(() -> {
            final ArrayList<Uri> uris = new ArrayList<>();
            try {
                JSONArray arr = new JSONArray(jsonUris);
                int limit = Math.min(arr.length(), 1000);
                for (int i = 0; i < limit; i++) {
                    Uri uri = Uri.parse(arr.getString(i));
                    int granted = activity.checkUriPermission(uri, android.os.Process.myPid(), android.os.Process.myUid(),
                            Intent.FLAG_GRANT_WRITE_URI_PERMISSION);
                    if (granted != PackageManager.PERMISSION_GRANTED) uris.add(uri);
                }
            } catch (Exception e) { callJs(cb, "false"); return; }
            if (uris.isEmpty()) { callJs(cb, "true"); return; }
            activity.runOnUiThread(() -> {
                synchronized (this) {
                    if (pendingWriteBatchCallback != null || pendingMove != null) { callJs(cb, "false"); return; }
                    pendingWriteBatchCallback = cb;
                }
                try {
                    PendingIntent request = MediaStore.createWriteRequest(activity.getContentResolver(), uris);
                    activity.startIntentSenderForResult(request.getIntentSender(), WRITE_BATCH_REQ, null, 0, 0, 0);
                } catch (Exception e) { finishWriteBatch(false); }
            });
        });
    }

    private void finishWriteBatch(boolean granted) {
        final String cb;
        synchronized (this) { cb = pendingWriteBatchCallback; pendingWriteBatchCallback = null; }
        if (cb != null) callJs(cb, granted ? "true" : "false");
    }

    @JavascriptInterface
    public String getMediaStoreVersion() {
        if (Build.VERSION.SDK_INT >= 29) {
            try { return MediaStore.getVersion(activity); } catch (Exception ignored) {}
        }
        return "";
    }

    @JavascriptInterface
    public long getMediaStoreGeneration() {
        if (Build.VERSION.SDK_INT >= 30) {
            try { return MediaStore.getGeneration(activity, MediaStore.VOLUME_EXTERNAL_PRIMARY); } catch (Exception ignored) {}
        }
        return -1L;
    }

    /* 相册列表异步读取：JS 首屏可先使用轻量缓存，不再等待完整 MediaStore 扫描 */
    @JavascriptInterface
    public void readAlbumsAsync(final String cb) {
        io.execute(() -> callJs(cb, readAlbumsSync()));
    }

    /* 保留同步接口兼容旧版 JS；优化版 app.js 优先使用 readAlbumsAsync */
    @JavascriptInterface
    public String readAlbums() {
        return readAlbumsSync();
    }

    private String readAlbumsSync() {
        JSONArray arr = new JSONArray();
        Map<String, JSONObject> map = new HashMap<>();
        try {
            if (hasImagePermission()) {
                scanAlbums(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, true, map);
            }
            if (hasVideoPermission()) {
                scanAlbums(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, false, map);
            }
            List<JSONObject> rows = new ArrayList<>(map.values());
            Collections.sort(rows, (a, b) -> Long.compare(b.optLong("_latest", 0L), a.optLong("_latest", 0L)));
            for (JSONObject o : rows) {
                o.remove("_latest");
                arr.put(o);
            }
        } catch (Exception ignored) {}
        return arr.toString();
    }

    private void scanAlbums(Uri collection, boolean isImage, Map<String, JSONObject> map) {
        Cursor c = null;
        try {
            String[] proj;
            if (Build.VERSION.SDK_INT >= 29) {
                proj = new String[]{
                        MediaStore.MediaColumns.BUCKET_ID,
                        MediaStore.MediaColumns.BUCKET_DISPLAY_NAME,
                        MediaStore.MediaColumns._ID,
                        MediaStore.MediaColumns.DATE_ADDED,
                        MediaStore.MediaColumns.RELATIVE_PATH
                };
            } else {
                proj = new String[]{
                        MediaStore.MediaColumns.BUCKET_ID,
                        MediaStore.MediaColumns.BUCKET_DISPLAY_NAME,
                        MediaStore.MediaColumns._ID,
                        MediaStore.MediaColumns.DATE_ADDED
                };
            }
            c = activity.getContentResolver().query(
                    collection, proj, null, null, MediaStore.MediaColumns.DATE_ADDED + " DESC");
            if (c == null) return;
            while (c.moveToNext()) {
                String bid = c.getString(0);
                String name = c.getString(1);
                long id = c.getLong(2);
                long date = c.isNull(3) ? 0L : c.getLong(3);
                if (bid == null) continue;

                boolean pica = false;
                if (Build.VERSION.SDK_INT >= 29) {
                    try {
                        String rp = c.getString(4);
                        pica = rp != null && rp.startsWith("Pictures/PicaPhoto/");
                    } catch (Exception ignored) {}
                }

                JSONObject o = map.get(bid);
                if (o == null) {
                    o = new JSONObject();
                    o.put("id", bid);
                    o.put("name", name == null ? "相册" : name);
                    o.put("count", 0);
                    o.put("cover", "");
                    o.put("pica", pica);
                    o.put("_latest", date);
                    map.put(bid, o);
                } else {
                    if (pica) o.put("pica", true);
                    if (date > o.optLong("_latest", 0L)) o.put("_latest", date);
                }
                o.put("count", o.getInt("count") + 1);

                /* 只为相册封面找一次系统缩略图，避免逐媒体 decode */
                if (o.optString("cover").isEmpty()) {
                    String th = thumbUri(isImage, id);
                    if (th != null) {
                        o.put("cover", th);
                    } else if (isImage) {
                        /* 极少数没有系统缩略图的相册先显示首图；网格本身不会再这样 fallback */
                        o.put("cover", ContentUris.withAppendedId(collection, id).toString());
                    }
                }
            }
        } catch (Exception ignored) {
        } finally {
            try { if (c != null) c.close(); } catch (Exception ignored) {}
        }
    }

    /* 媒体列表分页：统一从 MediaStore.Files 查询图片+视频，保持全局时间顺序。 */
    @JavascriptInterface
    public void readMediaPageAfterAsync(final String albumId, final long beforeDate, final long beforeId,
                                        final int limit, final String cb) {
        final int safeLimit = Math.max(24, Math.min(500, limit));
        io.execute(() -> callJs(cb, readMediaPageAfterSync(albumId, beforeDate, beforeId, safeLimit)));
    }

    /* offset 接口仅保留兼容旧版 JS；V2 使用上面的 keyset/cursor 分页。 */
    @JavascriptInterface
    public void readMediaPageAsync(final String albumId, final int offset, final int limit, final String cb) {
        final int safeOffset = Math.max(0, offset);
        final int safeLimit = Math.max(24, Math.min(500, limit));
        io.execute(() -> callJs(cb, readMediaPageOffsetSync(albumId, safeOffset, safeLimit)));
    }

    @JavascriptInterface
    public void readMediaAsync(final String albumId, final String cb) {
        io.execute(() -> callJs(cb, readMediaSync(albumId)));
    }

    private String readMediaSync(String albumId) {
        JSONArray all = new JSONArray();
        long beforeDate = -1L, beforeId = -1L;
        final int pageSize = 400;
        int guard = 0;
        try {
            while (guard++ < 10000) {
                JSONObject page = new JSONObject(readMediaPageAfterSync(albumId, beforeDate, beforeId, pageSize));
                JSONArray items = page.optJSONArray("items");
                if (items != null) {
                    for (int i = 0; i < items.length(); i++) all.put(items.get(i));
                }
                if (!page.optBoolean("hasMore", false)) break;
                long nd = page.optLong("nextBeforeDate", -1L);
                long ni = page.optLong("nextBeforeId", -1L);
                if (nd < 0 || ni < 0 || (nd == beforeDate && ni == beforeId)) break;
                beforeDate = nd;
                beforeId = ni;
            }
        } catch (Exception ignored) {}
        return all.toString();
    }

    private String readMediaPageAfterSync(String albumId, long beforeDate, long beforeId, int limit) {
        return queryMediaFilesPage(albumId, beforeDate, beforeId, 0, limit, false);
    }

    private String readMediaPageOffsetSync(String albumId, int offset, int limit) {
        return queryMediaFilesPage(albumId, -1L, -1L, offset, limit, true);
    }

    private String queryMediaFilesPage(String albumId, long beforeDate, long beforeId,
                                       int offset, int limit, boolean legacyOffset) {
        JSONObject out = new JSONObject();
        JSONArray arr = new JSONArray();
        Cursor c = null;
        try {
            boolean img = hasImagePermission();
            boolean vid = hasVideoPermission();
            if (!img && !vid) {
                out.put("items", arr);
                out.put("nextOffset", offset);
                out.put("hasMore", false);
                out.put("nextBeforeDate", -1L);
                out.put("nextBeforeId", -1L);
                return out.toString();
            }

            Uri files = Build.VERSION.SDK_INT >= 29
                    ? MediaStore.Files.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY)
                    : MediaStore.Files.getContentUri("external");
            String[] projection = {
                    MediaStore.MediaColumns._ID,
                    MediaStore.MediaColumns.DISPLAY_NAME,
                    MediaStore.MediaColumns.MIME_TYPE,
                    MediaStore.MediaColumns.SIZE,
                    MediaStore.MediaColumns.BUCKET_ID,
                    MediaStore.MediaColumns.BUCKET_DISPLAY_NAME,
                    MediaStore.MediaColumns.DATE_ADDED,
                    MediaStore.Files.FileColumns.MEDIA_TYPE,
                    Build.VERSION.SDK_INT >= 30 ? MediaStore.MediaColumns.GENERATION_MODIFIED : MediaStore.MediaColumns.DATE_MODIFIED
            };

            StringBuilder sel = new StringBuilder(MediaStore.MediaColumns.BUCKET_ID + "=? AND (");
            List<String> args = new ArrayList<>();
            args.add(albumId);
            if (img) {
                sel.append(MediaStore.Files.FileColumns.MEDIA_TYPE).append("=?");
                args.add(String.valueOf(MediaStore.Files.FileColumns.MEDIA_TYPE_IMAGE));
            }
            if (vid) {
                if (img) sel.append(" OR ");
                sel.append(MediaStore.Files.FileColumns.MEDIA_TYPE).append("=?");
                args.add(String.valueOf(MediaStore.Files.FileColumns.MEDIA_TYPE_VIDEO));
            }
            sel.append(")");
            if (!legacyOffset && beforeDate >= 0L && beforeId >= 0L) {
                sel.append(" AND (")
                        .append(MediaStore.MediaColumns.DATE_ADDED).append("<? OR (")
                        .append(MediaStore.MediaColumns.DATE_ADDED).append("=? AND ")
                        .append(MediaStore.MediaColumns._ID).append("<?))");
                args.add(String.valueOf(beforeDate));
                args.add(String.valueOf(beforeDate));
                args.add(String.valueOf(beforeId));
            }
            String[] selectionArgs = args.toArray(new String[0]);
            int requested = limit + 1;
            String order = MediaStore.MediaColumns.DATE_ADDED + " DESC, " + MediaStore.MediaColumns._ID + " DESC";

            if (!legacyOffset && Build.VERSION.SDK_INT >= 26) {
                Bundle q = new Bundle();
                q.putString(android.content.ContentResolver.QUERY_ARG_SQL_SELECTION, sel.toString());
                q.putStringArray(android.content.ContentResolver.QUERY_ARG_SQL_SELECTION_ARGS, selectionArgs);
                q.putStringArray(android.content.ContentResolver.QUERY_ARG_SORT_COLUMNS,
                        new String[]{MediaStore.MediaColumns.DATE_ADDED, MediaStore.MediaColumns._ID});
                q.putInt(android.content.ContentResolver.QUERY_ARG_SORT_DIRECTION,
                        android.content.ContentResolver.QUERY_SORT_DIRECTION_DESCENDING);
                q.putInt(android.content.ContentResolver.QUERY_ARG_LIMIT, requested);
                try {
                    c = activity.getContentResolver().query(files, projection, q, null);
                } catch (IllegalArgumentException unsupported) {
                    c = activity.getContentResolver().query(files, projection, sel.toString(), selectionArgs, order);
                }
            } else {
                c = activity.getContentResolver().query(files, projection, sel.toString(), selectionArgs, order);
            }

            if (c == null) {
                out.put("items", arr);
                out.put("nextOffset", offset);
                out.put("hasMore", false);
                out.put("nextBeforeDate", -1L);
                out.put("nextBeforeId", -1L);
                return out.toString();
            }
            if (legacyOffset && offset > 0) c.moveToPosition(Math.min(offset, c.getCount()) - 1);

            int ci = c.getColumnIndexOrThrow(MediaStore.MediaColumns._ID);
            int cn = c.getColumnIndexOrThrow(MediaStore.MediaColumns.DISPLAY_NAME);
            int cm = c.getColumnIndexOrThrow(MediaStore.MediaColumns.MIME_TYPE);
            int cs = c.getColumnIndex(MediaStore.MediaColumns.SIZE);
            int cb = c.getColumnIndex(MediaStore.MediaColumns.BUCKET_ID);
            int cbn = c.getColumnIndex(MediaStore.MediaColumns.BUCKET_DISPLAY_NAME);
            int cd = c.getColumnIndex(MediaStore.MediaColumns.DATE_ADDED);
            int ct = c.getColumnIndexOrThrow(MediaStore.Files.FileColumns.MEDIA_TYPE);
            String versionCol = Build.VERSION.SDK_INT >= 30 ? MediaStore.MediaColumns.GENERATION_MODIFIED : MediaStore.MediaColumns.DATE_MODIFIED;
            int cv = c.getColumnIndex(versionCol);

            int read = 0;
            boolean hasMore = false;
            long lastDate = -1L, lastId = -1L;
            while (c.moveToNext()) {
                if (read >= limit) { hasMore = true; break; }
                long id = c.getLong(ci);
                int mt = c.getInt(ct);
                boolean isImage = mt == MediaStore.Files.FileColumns.MEDIA_TYPE_IMAGE;
                Uri base = isImage ? MediaStore.Images.Media.EXTERNAL_CONTENT_URI : MediaStore.Video.Media.EXTERNAL_CONTENT_URI;
                long date = (cd >= 0 && !c.isNull(cd)) ? c.getLong(cd) : 0L;
                JSONObject o = new JSONObject();
                o.put("uri", ContentUris.withAppendedId(base, id).toString());
                String name = c.getString(cn);
                String mime = c.getString(cm);
                o.put("name", name == null ? "" : name);
                o.put("mime", mime == null ? "" : mime);
                if (cs >= 0 && !c.isNull(cs)) o.put("size", c.getLong(cs));
                o.put("isVideo", !isImage);
                o.put("dateAdded", date);
                if (cv >= 0 && !c.isNull(cv)) o.put("thumbVersion", c.getLong(cv));
                if (cb >= 0 && !c.isNull(cb)) o.put("albumId", c.getString(cb));
                if (cbn >= 0 && !c.isNull(cbn)) {
                    JSONArray names = new JSONArray();
                    names.put(c.getString(cbn));
                    o.put("albumNames", names);
                }
                arr.put(o);
                lastDate = date;
                lastId = id;
                read++;
            }

            out.put("items", arr);
            out.put("offset", offset);
            out.put("nextOffset", offset + read);
            out.put("hasMore", hasMore);
            out.put("nextBeforeDate", lastDate);
            out.put("nextBeforeId", lastId);
            out.put("mediaToken", getMediaStoreVersion() + "|" + getMediaStoreGeneration());
        } catch (Exception ignored) {
            try {
                out.put("items", arr);
                out.put("nextOffset", offset + arr.length());
                out.put("hasMore", false);
                out.put("nextBeforeDate", -1L);
                out.put("nextBeforeId", -1L);
            } catch (Exception ignored2) {}
        } finally {
            try { if (c != null) c.close(); } catch (Exception ignored) {}
        }
        return out.toString();
    }

    /* 旧的 queryInto 仍供“未整理”等特殊条件查询使用。 */
    private void queryInto(Uri uri, String sel, String[] args, JSONArray arr, boolean isImage) {
        if (isImage && !hasImagePermission()) return;
        if (!isImage && !hasVideoPermission()) return;
        Cursor c = null;
        try {
            String[] qp = {
                    MediaStore.MediaColumns._ID,
                    MediaStore.MediaColumns.DISPLAY_NAME,
                    MediaStore.MediaColumns.MIME_TYPE,
                    MediaStore.MediaColumns.SIZE,
                    MediaStore.MediaColumns.BUCKET_ID,
                    MediaStore.MediaColumns.BUCKET_DISPLAY_NAME,
                    MediaStore.MediaColumns.DATE_ADDED,
                    Build.VERSION.SDK_INT >= 30 ? MediaStore.MediaColumns.GENERATION_MODIFIED : MediaStore.MediaColumns.DATE_MODIFIED
            };
            c = activity.getContentResolver().query(uri, qp, sel, args, MediaStore.MediaColumns.DATE_ADDED + " DESC");
            if (c == null) return;
            int ci = c.getColumnIndexOrThrow(MediaStore.MediaColumns._ID);
            int cn = c.getColumnIndexOrThrow(MediaStore.MediaColumns.DISPLAY_NAME);
            int cm = c.getColumnIndexOrThrow(MediaStore.MediaColumns.MIME_TYPE);
            int csIdx = c.getColumnIndex(MediaStore.MediaColumns.SIZE);
            int cbIdx = c.getColumnIndex(MediaStore.MediaColumns.BUCKET_ID);
            int cbnIdx = c.getColumnIndex(MediaStore.MediaColumns.BUCKET_DISPLAY_NAME);
            int cdIdx = c.getColumnIndex(MediaStore.MediaColumns.DATE_ADDED);
            String versionCol = Build.VERSION.SDK_INT >= 30 ? MediaStore.MediaColumns.GENERATION_MODIFIED : MediaStore.MediaColumns.DATE_MODIFIED;
            int cvIdx = c.getColumnIndex(versionCol);
            Uri base = isImage ? MediaStore.Images.Media.EXTERNAL_CONTENT_URI : MediaStore.Video.Media.EXTERNAL_CONTENT_URI;
            while (c.moveToNext()) {
                long id = c.getLong(ci);
                JSONObject o = new JSONObject();
                o.put("uri", ContentUris.withAppendedId(base, id).toString());
                String name = c.getString(cn);
                String mime = c.getString(cm);
                o.put("name", name == null ? "" : name);
                o.put("mime", mime == null ? "" : mime);
                if (csIdx >= 0 && !c.isNull(csIdx)) o.put("size", c.getLong(csIdx));
                o.put("isVideo", !isImage);
                if (cdIdx >= 0 && !c.isNull(cdIdx)) o.put("dateAdded", c.getLong(cdIdx));
                if (cvIdx >= 0 && !c.isNull(cvIdx)) o.put("thumbVersion", c.getLong(cvIdx));
                if (cbIdx >= 0 && !c.isNull(cbIdx)) o.put("albumId", c.getString(cbIdx));
                if (cbnIdx >= 0 && !c.isNull(cbnIdx)) {
                    JSONArray names = new JSONArray();
                    names.put(c.getString(cbnIdx));
                    o.put("albumNames", names);
                }
                arr.put(o);
            }
        } catch (Exception ignored) {
        } finally {
            try { if (c != null) c.close(); } catch (Exception ignored) {}
        }
    }

    /* 创建相册文件夹（Pictures/PicaPhoto/名称），返回相对路径 */
    @JavascriptInterface
    public String createAlbum(String name) {
        if (name == null) name = "新相册";
        String safe = name.replaceAll("[\\\\/:*?\"<>|]", "_").trim();
        if (safe.isEmpty()) safe = "新相册";
        final String rel = "Pictures/PicaPhoto/" + safe + "/";
        if (Build.VERSION.SDK_INT >= 29) {
            io.execute(() -> {
                try {
                    ContentValues v = new ContentValues();
                    v.put(MediaStore.MediaColumns.DISPLAY_NAME, ".nomedia");
                    v.put(MediaStore.MediaColumns.MIME_TYPE, "text/plain");
                    v.put(MediaStore.MediaColumns.RELATIVE_PATH, rel);
                    v.put(MediaStore.MediaColumns.IS_PENDING, 1);
                    Uri out = activity.getContentResolver().insert(MediaStore.Files.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY), v);
                    if (out != null) {
                        ContentValues v2 = new ContentValues();
                        v2.put(MediaStore.MediaColumns.IS_PENDING, 0);
                        activity.getContentResolver().update(out, v2, null, null);
                        activity.getContentResolver().delete(out, null, null);
                    }
                } catch (Exception ignored) {}
            });
        } else {
            try {
                File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_PICTURES), "PicaPhoto/" + safe);
                if (!dir.exists()) dir.mkdirs();
            } catch (Exception ignored) {}
        }
        return rel;
    }

    @JavascriptInterface
    public void deleteEmptyAlbum(String name) {
        final String safe = (name == null ? "" : name).replaceAll("[\\\\/:*?\"<>|]", "_").trim();
        if (safe.isEmpty()) return;
        io.execute(() -> {
            try {
                File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_PICTURES),
                        "PicaPhoto/" + safe);
                File[] children = dir.listFiles();
                if (dir.exists() && (children == null || children.length == 0)) dir.delete();
            } catch (Exception ignored) {}
        });
    }

    /* 可见项按需缩略图：原生磁盘缓存，不再把图片 Base64 送进 JS/IndexedDB。 */
    @JavascriptInterface
    public void getMediaThumbV2Async(final String uriStr, final long version, final String cb) {
        io.execute(() -> {
            String thumb = getOrCreateMediaThumbUri(uriStr, version);
            try {
                JSONObject o = new JSONObject();
                o.put("uri", uriStr);
                o.put("thumb", thumb == null ? JSONObject.NULL : thumb);
                callJs(cb, o.toString());
            } catch (Exception ignored) {}
        });
    }

    @JavascriptInterface
    public void getMediaThumbAsync(final String uriStr, final String cb) {
        io.execute(() -> {
            String thumb = getOrCreateMediaThumbUri(uriStr, -1L);
            try {
                JSONObject o = new JSONObject();
                o.put("uri", uriStr);
                o.put("thumb", thumb == null ? JSONObject.NULL : thumb);
                callJs(cb, o.toString());
            } catch (Exception ignored) {}
        });
    }

    /* 兼容旧版 JS 名称 */
    @JavascriptInterface
    public void getVideoThumbAsync(final String uriStr, final String cb) {
        getMediaThumbAsync(uriStr, cb);
    }

    @JavascriptInterface
    public void clearThumbCache() {
        io.execute(this::clearThumbCacheSync);
    }

    /* WebView 本地缩略图资源：避免 file:// 跨路径差异，也不需要暴露外部存储。 */
    public WebResourceResponse interceptThumbRequest(Uri uri) {
        try {
            if (uri == null || !"https".equalsIgnoreCase(uri.getScheme()) ||
                    !"picaphoto.local".equalsIgnoreCase(uri.getHost())) return null;
            String path = uri.getPath();
            if (path == null || !path.startsWith("/thumb/")) return null;
            String name = path.substring("/thumb/".length());
            if (!name.matches("[0-9a-fA-F]+\\.jpg")) return null;
            File f = new File(thumbDir, name);
            if (!f.exists() || !f.isFile() || f.length() <= 0) return null;
            try { f.setLastModified(System.currentTimeMillis()); } catch (Exception ignored) {}
            return new WebResourceResponse("image/jpeg", null, new FileInputStream(f));
        } catch (Exception ignored) {
            return null;
        }
    }

    private String getOrCreateMediaThumbUri(String uriStr, long suppliedVersion) {
        Bitmap bmp = null;
        try {
            Uri u = Uri.parse(uriStr);
            long version = suppliedVersion >= 0L ? suppliedVersion : mediaItemGeneration(u);
            String key = sha1(uriStr + "|" + version);
            File outFile = new File(thumbDir, key + ".jpg");
            if (outFile.exists() && outFile.length() > 128) {
                try { outFile.setLastModified(System.currentTimeMillis()); } catch (Exception ignored) {}
                return "https://picaphoto.local/thumb/" + outFile.getName();
            }

            if (!thumbDir.exists() && !thumbDir.mkdirs()) return null;
            if (Build.VERSION.SDK_INT >= 29) {
                bmp = activity.getContentResolver().loadThumbnail(u, new Size(512, 512), null);
            } else if (isVideo(u)) {
                android.media.MediaMetadataRetriever r = new android.media.MediaMetadataRetriever();
                try {
                    r.setDataSource(activity, u);
                    bmp = r.getFrameAtTime(1000000, android.media.MediaMetadataRetriever.OPTION_CLOSEST_SYNC);
                } finally {
                    try { r.release(); } catch (Exception ignored) {}
                }
            } else {
                long id = ContentUris.parseId(u);
                bmp = MediaStore.Images.Thumbnails.getThumbnail(
                        activity.getContentResolver(), id, MediaStore.Images.Thumbnails.MINI_KIND, null);
            }
            if (bmp == null) return null;

            int max = 512;
            int bw = bmp.getWidth(), bh = bmp.getHeight();
            Bitmap scaled = bmp;
            if (bw > max || bh > max) {
                float scale = Math.min(max / (float) bw, max / (float) bh);
                int w = Math.max(1, Math.round(bw * scale));
                int h = Math.max(1, Math.round(bh * scale));
                scaled = Bitmap.createScaledBitmap(bmp, w, h, true);
            }

            File tmp = new File(thumbDir, key + ".tmp");
            boolean ok;
            try (FileOutputStream fos = new FileOutputStream(tmp)) {
                ok = scaled.compress(Bitmap.CompressFormat.JPEG, 78, fos);
                fos.flush();
            }
            if (scaled != bmp) scaled.recycle();
            bmp.recycle();
            bmp = null;
            if (!ok) { try { tmp.delete(); } catch (Exception ignored) {} return null; }
            if (outFile.exists()) outFile.delete();
            if (!tmp.renameTo(outFile)) {
                try { tmp.delete(); } catch (Exception ignored) {}
                return null;
            }
            try { outFile.setLastModified(System.currentTimeMillis()); } catch (Exception ignored) {}
            if ((thumbWrites.incrementAndGet() & 63) == 0) cleanupThumbCache();
            return "https://picaphoto.local/thumb/" + outFile.getName();
        } catch (Exception e) {
            try { if (bmp != null && !bmp.isRecycled()) bmp.recycle(); } catch (Exception ignored) {}
            return null;
        }
    }

    private long mediaItemGeneration(Uri uri) {
        Cursor c = null;
        try {
            String col = Build.VERSION.SDK_INT >= 30
                    ? MediaStore.MediaColumns.GENERATION_MODIFIED
                    : MediaStore.MediaColumns.DATE_MODIFIED;
            c = activity.getContentResolver().query(uri, new String[]{col}, null, null, null);
            if (c != null && c.moveToFirst() && !c.isNull(0)) return c.getLong(0);
        } catch (Exception ignored) {
        } finally {
            try { if (c != null) c.close(); } catch (Exception ignored) {}
        }
        return 0L;
    }

    private String sha1(String s) {
        try {
            MessageDigest md = MessageDigest.getInstance("SHA-1");
            byte[] b = md.digest(s.getBytes("UTF-8"));
            StringBuilder out = new StringBuilder(b.length * 2);
            for (byte x : b) out.append(String.format(java.util.Locale.US, "%02x", x & 0xff));
            return out.toString();
        } catch (Exception e) {
            return Integer.toHexString(s.hashCode());
        }
    }

    private void cleanupThumbCache() {
        try {
            File[] files = thumbDir.listFiles((dir, name) -> name.endsWith(".jpg"));
            if (files == null || files.length == 0) return;
            long total = 0L;
            for (File f : files) total += Math.max(0L, f.length());
            if (files.length <= THUMB_MAX_FILES && total <= THUMB_MAX_BYTES) return;
            Arrays.sort(files, (a, b) -> Long.compare(a.lastModified(), b.lastModified()));
            int count = files.length;
            for (File f : files) {
                if (count <= (THUMB_MAX_FILES * 3 / 4) && total <= THUMB_TARGET_BYTES) break;
                long len = Math.max(0L, f.length());
                if (f.delete()) { total -= len; count--; }
            }
        } catch (Exception ignored) {}
    }

    private void clearThumbCacheSync() {
        try {
            File[] files = thumbDir.listFiles();
            if (files != null) for (File f : files) { try { f.delete(); } catch (Exception ignored) {} }
        } catch (Exception ignored) {}
    }

    /* 查询某张照片所属相册（高亮 fallback；照片列表已自带 albumNames） */
    @JavascriptInterface
    public String readAlbumOf(String uriStr) {
        JSONArray arr = new JSONArray();
        try {
            Uri u = Uri.parse(uriStr);
            Cursor c = activity.getContentResolver().query(u, new String[]{MediaStore.MediaColumns.BUCKET_ID, MediaStore.MediaColumns.BUCKET_DISPLAY_NAME}, null, null, null);
            if (c != null && c.moveToFirst()) {
                String bid = c.getString(0);
                String name = c.getString(1);
                if (bid != null) {
                    JSONObject o = new JSONObject();
                    o.put("id", bid);
                    o.put("name", name == null ? "相册" : name);
                    arr.put(o);
                }
                c.close();
            }
        } catch (Exception ignored) {}
        return arr.toString();
    }

    /* 未整理照片：无相册归属 + 被“隐藏”的相册照片；V2 同样使用 keyset 分页。 */
    @JavascriptInterface
    public void readUnfiledPageAfterAsync(final String hiddenJson, final long beforeDate, final long beforeId,
                                          final int limit, final String cb) {
        final int safeLimit = Math.max(24, Math.min(500, limit));
        io.execute(() -> callJs(cb, readUnfiledPageAfterSync(hiddenJson, beforeDate, beforeId, safeLimit)));
    }

    @JavascriptInterface
    public void readUnfiledAsync(final String hiddenJson, final String cb) {
        io.execute(() -> {
            JSONArray all = new JSONArray();
            long beforeDate = -1L, beforeId = -1L;
            int guard = 0;
            try {
                while (guard++ < 10000) {
                    JSONObject page = new JSONObject(readUnfiledPageAfterSync(hiddenJson, beforeDate, beforeId, 400));
                    JSONArray items = page.optJSONArray("items");
                    if (items != null) for (int i = 0; i < items.length(); i++) all.put(items.get(i));
                    if (!page.optBoolean("hasMore", false)) break;
                    long nd = page.optLong("nextBeforeDate", -1L);
                    long ni = page.optLong("nextBeforeId", -1L);
                    if (nd < 0 || ni < 0 || (nd == beforeDate && ni == beforeId)) break;
                    beforeDate = nd; beforeId = ni;
                }
            } catch (Exception ignored) {}
            callJs(cb, all.toString());
        });
    }

    /** 首页只需要数量，不解码缩略图也不构造媒体 JSON。 */
    @JavascriptInterface
    public void readUnfiledCountAsync(final String hiddenJson, final String cb) {
        io.execute(() -> {
            int count = 0;
            Cursor c = null;
            try {
                boolean img = hasImagePermission(), vid = hasVideoPermission();
                if (!img && !vid) { callJs(cb, "0"); return; }
                Uri files = Build.VERSION.SDK_INT >= 29
                        ? MediaStore.Files.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY)
                        : MediaStore.Files.getContentUri("external");
                List<String> args = new ArrayList<>();
                StringBuilder sel = new StringBuilder("(")
                        .append(MediaStore.MediaColumns.BUCKET_DISPLAY_NAME).append(" IS NULL OR ")
                        .append(MediaStore.MediaColumns.BUCKET_DISPLAY_NAME).append("=''");
                try {
                    JSONArray hid = new JSONArray(hiddenJson == null ? "[]" : hiddenJson);
                    if (hid.length() > 0) {
                        sel.append(" OR ").append(MediaStore.MediaColumns.BUCKET_ID).append(" IN (");
                        for (int i = 0; i < hid.length(); i++) {
                            if (i > 0) sel.append(",");
                            sel.append("?"); args.add(hid.getString(i));
                        }
                        sel.append(")");
                    }
                } catch (Exception ignored) {}
                sel.append(") AND (");
                if (img) {
                    sel.append(MediaStore.Files.FileColumns.MEDIA_TYPE).append("=?");
                    args.add(String.valueOf(MediaStore.Files.FileColumns.MEDIA_TYPE_IMAGE));
                }
                if (vid) {
                    if (img) sel.append(" OR ");
                    sel.append(MediaStore.Files.FileColumns.MEDIA_TYPE).append("=?");
                    args.add(String.valueOf(MediaStore.Files.FileColumns.MEDIA_TYPE_VIDEO));
                }
                sel.append(")");
                c = activity.getContentResolver().query(files,
                        new String[]{MediaStore.MediaColumns._ID}, sel.toString(), args.toArray(new String[0]), null);
                if (c != null) count = c.getCount();
            } catch (Exception ignored) {
                count = 0;
            } finally {
                try { if (c != null) c.close(); } catch (Exception ignored) {}
            }
            callJs(cb, String.valueOf(count));
        });
    }

    private String readUnfiledPageAfterSync(String hiddenJson, long beforeDate, long beforeId, int limit) {
        JSONObject out = new JSONObject();
        JSONArray arr = new JSONArray();
        Cursor c = null;
        try {
            boolean img = hasImagePermission(), vid = hasVideoPermission();
            if (!img && !vid) {
                out.put("items", arr); out.put("hasMore", false);
                out.put("nextBeforeDate", -1L); out.put("nextBeforeId", -1L); out.put("nextOffset", 0);
                return out.toString();
            }
            Uri files = Build.VERSION.SDK_INT >= 29
                    ? MediaStore.Files.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY)
                    : MediaStore.Files.getContentUri("external");
            String versionCol = Build.VERSION.SDK_INT >= 30 ? MediaStore.MediaColumns.GENERATION_MODIFIED : MediaStore.MediaColumns.DATE_MODIFIED;
            String[] projection = {
                    MediaStore.MediaColumns._ID, MediaStore.MediaColumns.DISPLAY_NAME, MediaStore.MediaColumns.MIME_TYPE,
                    MediaStore.MediaColumns.BUCKET_ID, MediaStore.MediaColumns.BUCKET_DISPLAY_NAME,
                    MediaStore.MediaColumns.DATE_ADDED, MediaStore.MediaColumns.SIZE,
                    MediaStore.Files.FileColumns.MEDIA_TYPE, versionCol
            };

            List<String> args = new ArrayList<>();
            StringBuilder bucket = new StringBuilder("(")
                    .append(MediaStore.MediaColumns.BUCKET_DISPLAY_NAME).append(" IS NULL OR ")
                    .append(MediaStore.MediaColumns.BUCKET_DISPLAY_NAME).append("=''");
            try {
                JSONArray hid = new JSONArray(hiddenJson == null ? "[]" : hiddenJson);
                if (hid.length() > 0) {
                    bucket.append(" OR ").append(MediaStore.MediaColumns.BUCKET_ID).append(" IN (");
                    for (int i = 0; i < hid.length(); i++) {
                        if (i > 0) bucket.append(",");
                        bucket.append("?"); args.add(hid.getString(i));
                    }
                    bucket.append(")");
                }
            } catch (Exception ignored) {}
            bucket.append(")");

            StringBuilder sel = new StringBuilder(bucket).append(" AND (");
            if (img) {
                sel.append(MediaStore.Files.FileColumns.MEDIA_TYPE).append("=?");
                args.add(String.valueOf(MediaStore.Files.FileColumns.MEDIA_TYPE_IMAGE));
            }
            if (vid) {
                if (img) sel.append(" OR ");
                sel.append(MediaStore.Files.FileColumns.MEDIA_TYPE).append("=?");
                args.add(String.valueOf(MediaStore.Files.FileColumns.MEDIA_TYPE_VIDEO));
            }
            sel.append(")");
            if (beforeDate >= 0L && beforeId >= 0L) {
                sel.append(" AND (").append(MediaStore.MediaColumns.DATE_ADDED).append("<? OR (")
                        .append(MediaStore.MediaColumns.DATE_ADDED).append("=? AND ")
                        .append(MediaStore.MediaColumns._ID).append("<?))");
                args.add(String.valueOf(beforeDate)); args.add(String.valueOf(beforeDate)); args.add(String.valueOf(beforeId));
            }
            String[] selectionArgs = args.toArray(new String[0]);
            String order = MediaStore.MediaColumns.DATE_ADDED + " DESC, " + MediaStore.MediaColumns._ID + " DESC";
            int requested = limit + 1;
            if (Build.VERSION.SDK_INT >= 26) {
                Bundle q = new Bundle();
                q.putString(android.content.ContentResolver.QUERY_ARG_SQL_SELECTION, sel.toString());
                q.putStringArray(android.content.ContentResolver.QUERY_ARG_SQL_SELECTION_ARGS, selectionArgs);
                q.putStringArray(android.content.ContentResolver.QUERY_ARG_SORT_COLUMNS,
                        new String[]{MediaStore.MediaColumns.DATE_ADDED, MediaStore.MediaColumns._ID});
                q.putInt(android.content.ContentResolver.QUERY_ARG_SORT_DIRECTION,
                        android.content.ContentResolver.QUERY_SORT_DIRECTION_DESCENDING);
                q.putInt(android.content.ContentResolver.QUERY_ARG_LIMIT, requested);
                try { c = activity.getContentResolver().query(files, projection, q, null); }
                catch (IllegalArgumentException unsupported) {
                    c = activity.getContentResolver().query(files, projection, sel.toString(), selectionArgs, order);
                }
            } else {
                c = activity.getContentResolver().query(files, projection, sel.toString(), selectionArgs, order);
            }
            if (c == null) {
                out.put("items", arr); out.put("hasMore", false);
                out.put("nextBeforeDate", -1L); out.put("nextBeforeId", -1L); out.put("nextOffset", 0);
                return out.toString();
            }
            int ci=c.getColumnIndexOrThrow(MediaStore.MediaColumns._ID);
            int cn=c.getColumnIndexOrThrow(MediaStore.MediaColumns.DISPLAY_NAME);
            int cm=c.getColumnIndexOrThrow(MediaStore.MediaColumns.MIME_TYPE);
            int cb=c.getColumnIndex(MediaStore.MediaColumns.BUCKET_ID);
            int cbn=c.getColumnIndex(MediaStore.MediaColumns.BUCKET_DISPLAY_NAME);
            int cd=c.getColumnIndex(MediaStore.MediaColumns.DATE_ADDED);
            int cs=c.getColumnIndex(MediaStore.MediaColumns.SIZE);
            int ct=c.getColumnIndexOrThrow(MediaStore.Files.FileColumns.MEDIA_TYPE);
            int cv=c.getColumnIndex(versionCol);
            int read=0; boolean hasMore=false; long lastDate=-1L,lastId=-1L;
            while(c.moveToNext()){
                if(read>=limit){ hasMore=true; break; }
                long id=c.getLong(ci); int mt=c.getInt(ct);
                boolean isImage=mt==MediaStore.Files.FileColumns.MEDIA_TYPE_IMAGE;
                Uri base=isImage?MediaStore.Images.Media.EXTERNAL_CONTENT_URI:MediaStore.Video.Media.EXTERNAL_CONTENT_URI;
                long date=(cd>=0&&!c.isNull(cd))?c.getLong(cd):0L;
                JSONObject o=new JSONObject();
                o.put("uri",ContentUris.withAppendedId(base,id).toString());
                String name=c.getString(cn),mime=c.getString(cm);
                o.put("name",name==null?"":name); o.put("mime",mime==null?"":mime); o.put("isVideo",!isImage);
                if(cs>=0&&!c.isNull(cs))o.put("size",c.getLong(cs));
                o.put("dateAdded",date); if(cv>=0&&!c.isNull(cv))o.put("thumbVersion",c.getLong(cv));
                if(cb>=0&&!c.isNull(cb))o.put("albumId",c.getString(cb));
                if(cbn>=0&&!c.isNull(cbn)){ JSONArray names=new JSONArray(); names.put(c.getString(cbn)); o.put("albumNames",names); }
                arr.put(o); lastDate=date; lastId=id; read++;
            }
            out.put("items",arr); out.put("nextOffset",read); out.put("hasMore",hasMore);
            out.put("nextBeforeDate",lastDate); out.put("nextBeforeId",lastId);
            out.put("mediaToken",getMediaStoreVersion()+"|"+getMediaStoreGeneration());
        } catch(Exception ignored){
            try{ out.put("items",arr); out.put("hasMore",false); out.put("nextBeforeDate",-1L); out.put("nextBeforeId",-1L); out.put("nextOffset",arr.length()); }catch(Exception ignored2){}
        } finally { try{ if(c!=null)c.close(); }catch(Exception ignored){} }
        return out.toString();
    }

    /* 移动照片到相册。Android 11+ 的第三方媒体必须先取得系统写入授权。 */
    private boolean moveMedia(Uri src, String rel) {
        if (Build.VERSION.SDK_INT >= 29) {
            try {
                ContentValues v = new ContentValues();
                v.put(MediaStore.MediaColumns.RELATIVE_PATH, rel);
                return activity.getContentResolver().update(src, v, null, null) > 0;
            } catch (SecurityException e) { throw e; }
              catch (Exception e) { return false; }
        }
        try {
            Cursor c = activity.getContentResolver().query(src, new String[]{MediaStore.MediaColumns.DATA}, null, null, null);
            if (c != null && c.moveToFirst()) {
                String path = c.getString(0);
                c.close();
                if (path != null) {
                    File f = new File(path);
                    String sub = rel.startsWith("Pictures/") ? rel.substring("Pictures/".length()) : rel;
                    File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_PICTURES), sub);
                    if (!dir.exists()) dir.mkdirs();
                    File dst = new File(dir, f.getName());
                    return f.renameTo(dst);
                }
            } else if (c != null) { c.close(); }
        } catch (Exception e) { return false; }
        return false;
    }

    /* Rename a PicaPhoto-created album: move all items in the bucket to the new RELATIVE_PATH (true move). */
    @JavascriptInterface
    public void renameAlbumAsync(final String albumId, final String oldName, final String newName, final String cb) {
        io.execute(() -> {
            boolean ok = false;
            try {
                String safeOld = oldName.replaceAll("[\\\\/:*?\"<>|]", "_").trim();
                String safeNew = newName.replaceAll("[\\\\/:*?\"<>|]", "_").trim();
                if (safeOld.isEmpty() || safeNew.isEmpty()) { callJs(cb, "false"); return; }
                if (Build.VERSION.SDK_INT >= 29) {
                    String newRel = "Pictures/PicaPhoto/" + safeNew + "/";
                    createAlbumSync(safeNew);
                    Uri[] colls = {MediaStore.Images.Media.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY),
                                   MediaStore.Video.Media.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY)};
                    int moved = 0;
                    for (Uri coll : colls) {
                        Cursor c = activity.getContentResolver().query(coll,
                                new String[]{MediaStore.MediaColumns._ID},
                                MediaStore.MediaColumns.BUCKET_ID + "=?", new String[]{albumId}, null);
                        if (c != null) {
                            while (c.moveToNext()) {
                                long id = c.getLong(0);
                                Uri item = ContentUris.withAppendedId(coll, id);
                                ContentValues v = new ContentValues();
                                v.put(MediaStore.MediaColumns.RELATIVE_PATH, newRel);
                                try { if (activity.getContentResolver().update(item, v, null, null) > 0) moved++; } catch (Exception ignored) {}
                            }
                            c.close();
                        }
                    }
                    ok = moved > 0;
                    if (ok) {
                        try {
                            File oldDir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_PICTURES), "PicaPhoto/" + safeOld);
                            if (oldDir.exists()) oldDir.delete();
                        } catch (Exception ignored) {}
                    }
                } else {
                    File root = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_PICTURES), "PicaPhoto");
                    File oldDir = new File(root, safeOld);
                    File newDir = new File(root, safeNew);
                    if (oldDir.exists() && !newDir.exists()) ok = oldDir.renameTo(newDir);
                }
            } catch (Exception ignored) {}
            callJs(cb, String.valueOf(ok));
        });
    }

    @JavascriptInterface
    public void moveToAlbumAsync(final String albumName, final String jsonUris, final String cb) {
        requestMove(jsonUris, createAlbumSync(albumName), cb);
    }

    @JavascriptInterface
    public void moveToPathAsync(final String jsonUris, final String relativePath, final String cb) {
        requestMove(jsonUris, relativePath, cb);
    }

    private void requestMove(final String jsonUris, final String relativePath, final String cb) {
        if (Build.VERSION.SDK_INT < 30) {
            io.execute(() -> callJs(cb, moveToPathSync(jsonUris, relativePath)));
            return;
        }
        /* First try RELATIVE_PATH directly.  A granted URI (or media owned by this app)
           must not show another system confirmation on every move. */
        io.execute(() -> {
            String first = moveToPathSync(jsonUris, relativePath);
            ArrayList<Uri> denied = permissionUris(first);
            if (denied.isEmpty()) { callJs(cb, first); return; }
            requestWritePermission(jsonUris, relativePath, cb, first, denied);
        });
    }

    private void requestWritePermission(final String jsonUris, final String relativePath, final String cb,
                                        final String firstResults, final ArrayList<Uri> uris) {
        activity.runOnUiThread(() -> {
            synchronized (this) {
                if (pendingMove != null) {
                    callJs(cb, errorResults(jsonUris, "move_in_progress"));
                    return;
                }
                pendingMove = new PendingMove(jsonUris, relativePath, cb, firstResults);
            }
            try {
                PendingIntent request = MediaStore.createWriteRequest(activity.getContentResolver(), uris);
                activity.startIntentSenderForResult(request.getIntentSender(), WRITE_REQ, null, 0, 0, 0);
            } catch (IntentSender.SendIntentException e) {
                finishPendingMove(false);
            } catch (Exception e) {
                finishPendingMove(false);
            }
        });
    }

    private ArrayList<Uri> permissionUris(String results) {
        ArrayList<Uri> uris = new ArrayList<>();
        try {
            JSONArray arr = new JSONArray(results);
            for (int i = 0; i < arr.length(); i++) {
                JSONObject r = arr.getJSONObject(i);
                if ("needs_write_permission".equals(r.optString("err"))) uris.add(Uri.parse(r.getString("uri")));
            }
        } catch (Exception ignored) {}
        return uris;
    }

    public void onActivityResult(int requestCode, int resultCode) {
        if (requestCode == WRITE_REQ) finishPendingMove(resultCode == Activity.RESULT_OK);
        if (requestCode == WRITE_BATCH_REQ) finishWriteBatch(resultCode == Activity.RESULT_OK);
    }

    private void finishPendingMove(boolean granted) {
        final PendingMove move;
        synchronized (this) { move = pendingMove; pendingMove = null; }
        if (move == null) return;
        io.execute(() -> {
            String retried = granted ? moveToPathSync(move.jsonUris, move.relativePath)
                                     : errorResults(move.jsonUris, "write_permission_denied");
            callJs(move.callback, mergeMoveResults(move.firstResults, retried));
        });
    }

    private String mergeMoveResults(String first, String retried) {
        try {
            JSONArray a = new JSONArray(first), b = new JSONArray(retried), out = new JSONArray();
            java.util.HashMap<String, JSONObject> retriedByUri = new java.util.HashMap<>();
            for (int i = 0; i < b.length(); i++) { JSONObject r = b.getJSONObject(i); retriedByUri.put(r.optString("uri"), r); }
            for (int i = 0; i < a.length(); i++) {
                JSONObject r = a.getJSONObject(i);
                out.put("needs_write_permission".equals(r.optString("err")) ? retriedByUri.get(r.optString("uri")) : r);
            }
            return out.toString();
        } catch (Exception ignored) { return retried; }
    }

    private String errorResults(String jsonUris, String reason) {
        JSONArray out = new JSONArray();
        try {
            JSONArray uris = new JSONArray(jsonUris);
            for (int i = 0; i < uris.length(); i++) {
                JSONObject r = new JSONObject();
                r.put("uri", uris.getString(i));
                r.put("ok", false);
                r.put("err", reason);
                out.put(r);
            }
        } catch (Exception ignored) {}
        return out.toString();
    }

    private String moveToPathSync(String jsonUris, String relativePath) {
        JSONArray out = new JSONArray();
        try {
            JSONArray uris = new JSONArray(jsonUris);
            for (int i = 0; i < uris.length(); i++) {
                String us = uris.getString(i);
                JSONObject r = new JSONObject();
                r.put("uri", us);
                try {
                    Uri src = Uri.parse(us);
                    String oldPath = mediaRelativePath(src);
                    boolean ok = moveMedia(src, relativePath);
                    r.put("ok", ok);
                    if (oldPath != null) r.put("from", oldPath);
                    if (!ok) r.put("err", "move_failed");
                } catch (SecurityException e) { r.put("ok", false); r.put("err", "needs_write_permission"); }
                  catch (Exception e) { r.put("ok", false); r.put("err", String.valueOf(e)); }
                out.put(r);
            }
        } catch (Exception ignored) {}
        return out.toString();
    }

    private String mediaRelativePath(Uri src) {
        Cursor c = null;
        try {
            c = activity.getContentResolver().query(src,
                    new String[]{MediaStore.MediaColumns.RELATIVE_PATH}, null, null, null);
            if (c != null && c.moveToFirst()) return c.getString(0);
        } catch (Exception ignored) {
        } finally {
            if (c != null) try { c.close(); } catch (Exception ignored) {}
        }
        return null;
    }

    private String createAlbumSync(String name) {
        if (name == null) name = "新相册";
        String safe = name.replaceAll("[\\\\/:*?\"<>|]", "_").trim();
        if (safe.isEmpty()) safe = "新相册";
        String rel = "Pictures/PicaPhoto/" + safe + "/";
        if (Build.VERSION.SDK_INT >= 29) {
            try {
                ContentValues v = new ContentValues();
                v.put(MediaStore.MediaColumns.DISPLAY_NAME, ".nomedia");
                v.put(MediaStore.MediaColumns.MIME_TYPE, "text/plain");
                v.put(MediaStore.MediaColumns.RELATIVE_PATH, rel);
                v.put(MediaStore.MediaColumns.IS_PENDING, 1);
                Uri out = activity.getContentResolver().insert(MediaStore.Files.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY), v);
                if (out != null) {
                    ContentValues v2 = new ContentValues();
                    v2.put(MediaStore.MediaColumns.IS_PENDING, 0);
                    activity.getContentResolver().update(out, v2, null, null);
                    activity.getContentResolver().delete(out, null, null);
                }
            } catch (Exception ignored) {}
            return rel;
        } else {
            File dir = null;
            try {
                dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_PICTURES), "PicaPhoto/" + safe);
                if (!dir.exists()) dir.mkdirs();
            } catch (Exception ignored) {}
            return dir != null ? dir.getAbsolutePath() + "/" : rel;
        }
    }

    /* 把照片移出相册到 PicaPhoto 整理区（后台线程 + 回调） */
    @JavascriptInterface
    public void moveOutAlbumAsync(final String jsonUris, final String cb) {
        requestMove(jsonUris, "Pictures/PicaPhoto/", cb);
    }

    /* 状态栏高度（dp） */
    @JavascriptInterface
    public int getStatusBarHeight(){
        try {
            int id = activity.getResources().getIdentifier("status_bar_height", "dimen", "android");
            if (id > 0) {
                int px = activity.getResources().getDimensionPixelSize(id);
                float d = activity.getResources().getDisplayMetrics().density;
                return d > 0 ? Math.round(px / d) : px;
            }
        } catch (Exception ignored) {}
        return 0;
    }

    /* 导航栏高度（dp） */
    @JavascriptInterface
    public int getNavBarHeight(){
        try {
            int id = activity.getResources().getIdentifier("navigation_bar_height", "dimen", "android");
            if (id > 0) {
                int px = activity.getResources().getDimensionPixelSize(id);
                float d = activity.getResources().getDisplayMetrics().density;
                return d > 0 ? Math.round(px / d) : px;
            }
        } catch (Exception ignored) {}
        return 0;
    }

    /* 状态栏图标亮暗 */
    @JavascriptInterface
    public void setStatusBarDark(boolean dark){
        activity.runOnUiThread(() -> {
            try {
                if (Build.VERSION.SDK_INT >= 23) {
                    View decor = activity.getWindow().getDecorView();
                    int flags = decor.getSystemUiVisibility();
                    if (dark) flags |= View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR;
                    else flags &= ~View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR;
                    decor.setSystemUiVisibility(flags);
                }
            } catch (Exception ignored) {}
        });
    }

    /* 导航栏图标亮暗 */
    @JavascriptInterface
    public void setNavBarDark(boolean dark){
        activity.runOnUiThread(() -> {
            try {
                if (Build.VERSION.SDK_INT >= 26) {
                    View decor = activity.getWindow().getDecorView();
                    int flags = decor.getSystemUiVisibility();
                    if (dark) flags |= View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR;
                    else flags &= ~View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR;
                    decor.setSystemUiVisibility(flags);
                }
            } catch (Exception ignored) {}
        });
    }

    /* 系统深色模式 */
    @JavascriptInterface
    public boolean isSystemDark() {
        try {
            int mode = activity.getResources().getConfiguration().uiMode & android.content.res.Configuration.UI_MODE_NIGHT_MASK;
            return mode == android.content.res.Configuration.UI_MODE_NIGHT_YES;
        } catch (Exception e) { return false; }
    }

    /* 当前安装版本号 */
    @JavascriptInterface
    public String getAppVersion() {
        try { return BuildConfig.VERSION_NAME; } catch (Exception e) { return ""; }
    }

    /* 真正删除系统照片（Android 10+ 系统确认） */
    @JavascriptInterface
    public void requestDelete(String jsonUris) {
        try {
            JSONArray arr = new JSONArray(jsonUris);
            List<Uri> uris = new ArrayList<>();
            for (int i = 0; i < arr.length(); i++) uris.add(Uri.parse(arr.getString(i)));
            if (uris.isEmpty()) return;
            if (Build.VERSION.SDK_INT >= 30) {
                android.app.PendingIntent pi = MediaStore.createDeleteRequest(activity.getContentResolver(), uris);
                pendingDeleteUris = uris;
                activity.startIntentSenderForResult(pi.getIntentSender(), DELETE_REQ, null, 0, 0, 0);
            } else if (Build.VERSION.SDK_INT == 29) {
                try {
                    List<Uri> failed = new ArrayList<>();
                    for (Uri u : uris) {
                        try { activity.getContentResolver().delete(u, null, null); }
                        catch (android.app.RecoverableSecurityException e) { failed.add(u); }
                    }
                    if (!failed.isEmpty()) {
                        pendingDeleteUris = failed;
                        android.app.PendingIntent pi = recoverActionIntent(failed.get(0));
                        if (pi != null) {
                            activity.startIntentSenderForResult(pi.getIntentSender(), DELETE_REQ, null, 0, 0, 0);
                        }
                    }
                } catch (Exception ignored) {}
            } else {
                for (Uri u : uris) activity.getContentResolver().delete(u, null, null);
            }
        } catch (Exception e) {
            toast("删除失败：" + e.getMessage());
        }
    }

    private android.app.PendingIntent recoverActionIntent(Uri u) {
        try {
            try { activity.getContentResolver().delete(u, null, null); return null; }
            catch (android.app.RecoverableSecurityException e) { return e.getUserAction().getActionIntent(); }
        } catch (Exception e) { return null; }
    }

    /* 自动更新：下载最新 APK 并提示安装 */
    @JavascriptInterface
    public void downloadAndInstall(String url) {
        try {
            File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS), "PicaPhoto");
            if (!dir.exists()) dir.mkdirs();
            lastApk = new File(dir, "PicaPhoto_update.apk");
            if (lastApk.exists()) lastApk.delete();
            DownloadManager dm = (DownloadManager) activity.getSystemService(Context.DOWNLOAD_SERVICE);
            DownloadManager.Request req = new DownloadManager.Request(Uri.parse(url));
            req.setTitle("PicaPhoto 新版本");
            req.setDescription("下载完成后自动提示安装");
            req.setNotificationVisibility(DownloadManager.Request.VISIBILITY_VISIBLE_NOTIFY_COMPLETED);
            req.setAllowedOverMetered(true);
            req.setDestinationUri(Uri.fromFile(lastApk));
            pendingId = dm.enqueue(req);
            if (receiver == null) {
                receiver = new BroadcastReceiver() {
                    @Override
                    public void onReceive(Context c, Intent it) {
                        if (!DownloadManager.ACTION_DOWNLOAD_COMPLETE.equals(it.getAction())) return;
                        long done = it.getLongExtra(DownloadManager.EXTRA_DOWNLOAD_ID, -1);
                        if (done != pendingId) return;
                        DownloadManager dm2 = (DownloadManager) c.getSystemService(Context.DOWNLOAD_SERVICE);
                        boolean ok = false;
                        try {
                            DownloadManager.Query q = new DownloadManager.Query();
                            q.setFilterById(done);
                            Cursor cur = dm2.query(q);
                            if (cur != null) {
                                if (cur.moveToFirst()) {
                                    int st = cur.getInt(cur.getColumnIndexOrThrow(DownloadManager.COLUMN_STATUS));
                                    ok = (st == DownloadManager.STATUS_SUCCESSFUL);
                                }
                                cur.close();
                            }
                        } catch (Exception ignored) {}
                        if (ok) openInstall();
                        else toast("下载失败，请检查网络后重试");
                    }
                };
                activity.registerReceiver(receiver, new IntentFilter(DownloadManager.ACTION_DOWNLOAD_COMPLETE));
            }
            toast("已开始下载更新");
        } catch (Exception e) {
            toast("下载失败：" + e.getMessage());
        }
    }

    private void openInstall() {
        try {
            if (Build.VERSION.SDK_INT >= 26 && !activity.getPackageManager().canRequestPackageInstalls()) {
                try {
                    Intent si = new Intent(Settings.ACTION_MANAGE_UNKNOWN_APP_SOURCES, Uri.parse("package:" + activity.getPackageName()));
                    activity.startActivity(si);
                } catch (Exception e) {
                    toast("请在系统设置中允许安装未知来源应用");
                }
                return;
            }
            Intent intent = new Intent(Intent.ACTION_VIEW);
            Uri apkUri = FileProvider.getUriForFile(activity, "com.picaphoto.app.fileprovider", lastApk);
            intent.setDataAndType(apkUri, "application/vnd.android.package-archive");
            intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_GRANT_READ_URI_PERMISSION);
            activity.startActivity(intent);
        } catch (Exception e) {
            toast("请到下载目录手动安装：" + lastApk);
        }
    }

    private void toast(String msg) {
        activity.runOnUiThread(() -> Toast.makeText(activity, msg, Toast.LENGTH_SHORT).show());
    }

    private String copyMedia(Uri src, String rel, boolean video) {
        String name = queryName(src);
        String mime = activity.getContentResolver().getType(src);
        if (mime == null) mime = video ? "video/mp4" : "image/jpeg";
        if (Build.VERSION.SDK_INT >= 29) {
            Uri out = null;
            try {
                ContentValues v = new ContentValues();
                v.put(MediaStore.MediaColumns.DISPLAY_NAME, name);
                v.put(MediaStore.MediaColumns.MIME_TYPE, mime);
                v.put(MediaStore.MediaColumns.RELATIVE_PATH, rel);
                v.put(MediaStore.MediaColumns.IS_PENDING, 1);
                Uri collection = video ? MediaStore.Video.Media.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY)
                                       : MediaStore.Images.Media.getContentUri(MediaStore.VOLUME_EXTERNAL_PRIMARY);
                out = activity.getContentResolver().insert(collection, v);
                if (out == null) return null;
                try (InputStream in = activity.getContentResolver().openInputStream(src);
                     OutputStream os = activity.getContentResolver().openOutputStream(out)) {
                    if (in == null || os == null) return null;
                    byte[] buf = new byte[65536]; int n;
                    while ((n = in.read(buf)) > 0) os.write(buf, 0, n);
                }
                ContentValues v2 = new ContentValues();
                v2.put(MediaStore.MediaColumns.IS_PENDING, 0);
                activity.getContentResolver().update(out, v2, null, null);
                return out.toString();
            } catch (Exception e) {
                try { if (out != null) activity.getContentResolver().delete(out, null, null); } catch (Exception ignored) {}
                return null;
            }
        } else {
            try {
                File dir = new File(rel);
                if (!dir.exists()) dir.mkdirs();
                File f = new File(dir, name);
                if (f.exists()) f = new File(dir, System.currentTimeMillis() + "_" + name);
                try (InputStream in = activity.getContentResolver().openInputStream(src);
                     OutputStream os = new java.io.FileOutputStream(f)) {
                    if (in == null) return null;
                    byte[] buf = new byte[65536]; int n;
                    while ((n = in.read(buf)) > 0) os.write(buf, 0, n);
                }
                return f.getAbsolutePath();
            } catch (Exception e) { return null; }
        }
    }

    private String thumbUri(boolean isImage, long id) {
        try {
            Uri coll = isImage ? MediaStore.Images.Thumbnails.EXTERNAL_CONTENT_URI : MediaStore.Video.Thumbnails.EXTERNAL_CONTENT_URI;
            String colId = isImage ? MediaStore.Images.Thumbnails.IMAGE_ID : MediaStore.Video.Thumbnails.VIDEO_ID;
            Cursor c = activity.getContentResolver().query(coll, new String[]{MediaStore.Images.Thumbnails._ID}, colId + "=?", new String[]{String.valueOf(id)}, null);
            if (c != null) {
                if (c.moveToFirst()) {
                    long tid = c.getLong(0);
                    c.close();
                    return ContentUris.withAppendedId(coll, tid).toString();
                }
                c.close();
            }
        } catch (Exception ignored) {}
        return null;
    }

    private String queryName(Uri uri) {
        try {
            Cursor c = activity.getContentResolver().query(uri, new String[]{MediaStore.MediaColumns.DISPLAY_NAME}, null, null, null);
            if (c != null && c.moveToFirst()) { String n = c.getString(0); c.close(); return n; }
        } catch (Exception ignored) {}
        return "PicaPhoto_" + System.currentTimeMillis() + ".jpg";
    }
}
