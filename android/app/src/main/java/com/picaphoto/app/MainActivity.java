package com.picaphoto.app;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.view.Gravity;
import android.widget.FrameLayout;
import android.widget.TextView;
import android.content.Intent;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.view.View;
import android.view.WindowManager;
import android.webkit.JsResult;
import android.webkit.WebChromeClient;
import android.webkit.WebSettings;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebView;
import android.webkit.WebViewClient;

public class MainActivity extends Activity {
    private WebView web;
    private MediaBridge bridge;

    @SuppressLint("SetJavaScriptEnabled")
    @Override
    protected void onCreate(Bundle b) {
        super.onCreate(b);

        // 刘海 / 水滴 / 挖孔屏适配：内容延伸到挖孔区，交给 CSS safe-area 避让
        if (Build.VERSION.SDK_INT >= 28) {
            WindowManager.LayoutParams lp = getWindow().getAttributes();
            lp.layoutInDisplayCutoutMode = WindowManager.LayoutParams.LAYOUT_IN_DISPLAY_CUTOUT_MODE_SHORT_EDGES;
            getWindow().setAttributes(lp);
        }
        // 沉浸式全屏：内容延伸到状态栏/导航栏，状态栏图标颜色由 JS 按主题控制
        if (Build.VERSION.SDK_INT >= 30) {
            getWindow().setDecorFitsSystemWindows(false);
        } else {
            View decor = getWindow().getDecorView();
            decor.setSystemUiVisibility(View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN | View.SYSTEM_UI_FLAG_LAYOUT_STABLE);
        }
        getWindow().setStatusBarColor(android.graphics.Color.TRANSPARENT);
        getWindow().setNavigationBarColor(android.graphics.Color.TRANSPARENT);

        web = new WebView(this);
        final FrameLayout root = new FrameLayout(this);
        /* 启动画面：页面加载期间显示品牌色，避免白屏 */
        final TextView splash = new TextView(this);
        splash.setText("PicaPhoto");
        splash.setTextSize(26);
        splash.setGravity(Gravity.CENTER);
        splash.setTextColor(0xFFFFFFFF);
        splash.setBackgroundColor(0xFF2E58E8);
        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setAllowFileAccess(true);
        s.setAllowContentAccess(true);
        s.setMediaPlaybackRequiresUserGesture(false);
        s.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW);
        s.setCacheMode(WebSettings.LOAD_DEFAULT);
        // WebView 跟随系统深色仅由 CSS 控制，避免双重算法变暗
        if (Build.VERSION.SDK_INT >= 29) {
            s.setForceDark(WebSettings.FORCE_DARK_OFF);
        }
        if (Build.VERSION.SDK_INT >= 33) {
            s.setAlgorithmicDarkeningAllowed(false);
        }
        // 仅调试包开启 WebView 调试，正式发布不暴露
        if (BuildConfig.DEBUG) {
            web.setWebContentsDebuggingEnabled(true);
        }

        /* 支持 JS 的 alert/confirm：Android WebView 默认不弹窗，导致删除/清空等 confirm 全部无反应 */
        web.setWebChromeClient(new WebChromeClient() {
            @Override
            public boolean onJsConfirm(WebView view, String url, String message, JsResult result) {
                new AlertDialog.Builder(view.getContext())
                        .setMessage(message)
                        .setPositiveButton("确定", (d, w) -> result.confirm())
                        .setNegativeButton("取消", (d, w) -> result.cancel())
                        .setOnCancelListener(d -> result.cancel())
                        .show();
                return true;
            }
            @Override
            public boolean onJsAlert(WebView view, String url, String message, JsResult result) {
                new AlertDialog.Builder(view.getContext())
                        .setMessage(message)
                        .setPositiveButton("确定", (d, w) -> result.confirm())
                        .setOnCancelListener(d -> result.cancel())
                        .show();
                return true;
            }
        });

        web.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest request) {
                try {
                    if (bridge != null && request != null) {
                        WebResourceResponse r = bridge.interceptThumbRequest(request.getUrl());
                        if (r != null) return r;
                    }
                } catch (Exception ignored) {}
                return super.shouldInterceptRequest(view, request);
            }
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, String url) {
                try {
                    if (bridge != null && url != null) {
                        WebResourceResponse r = bridge.interceptThumbRequest(Uri.parse(url));
                        if (r != null) return r;
                    }
                } catch (Exception ignored) {}
                return super.shouldInterceptRequest(view, url);
            }
            @Override
            public void onPageFinished(WebView view, String url) {
                /* HTML 加载完成不等于应用数据已就绪。
                   正常由 JS init 首帧调用 Android.appReady() 移除；4 秒仅作为异常兜底。 */
                splash.postDelayed(() -> {
                    if (splash.getParent() != null) root.removeView(splash);
                }, 4000);
            }
            @Override
            public boolean shouldOverrideUrlLoading(WebView view, String url) {
                if (url.startsWith("file://") || url.startsWith("content://") || url.startsWith("https://picaphoto.local/")) return false;
                try {
                    startActivity(new Intent(Intent.ACTION_VIEW, Uri.parse(url)));
                } catch (Exception ignored) {}
                return true;
            }
        });

        // 原生桥接：系统相册读取 / 移动 / 删除 / 更新安装（后台线程完成后回调查看）
        bridge = new MediaBridge(this);
        bridge.attachWeb(web);
        bridge.setAppReadyCallback(() -> {
            if (splash.getParent() != null) root.removeView(splash);
        });
        web.addJavascriptInterface(bridge, "Android");

        root.addView(splash, new FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT));
        root.addView(web);
        setContentView(root);

        if (b != null && web != null) {
            web.restoreState(b);   // 从后台恢复：直接还原页面状态，避免重新加载白屏
            root.removeView(splash);   // 已恢复页面，立即移除启动画面
        } else {
            web.loadUrl("file:///android_asset/www/index.html");
        }
    }

    @Override
    public void onConfigurationChanged(android.content.res.Configuration newConfig) {
        super.onConfigurationChanged(newConfig);
        if (web != null) {
            web.evaluateJavascript("if(window.__sysDarkChanged){window.__sysDarkChanged();}", null);
        }
    }

    @Override
    protected void onSaveInstanceState(android.os.Bundle outState) {
        if (web != null) web.saveState(outState);
        super.onSaveInstanceState(outState);
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        if (bridge != null) bridge.onPermissionResult(requestCode);
        if ((requestCode == MediaBridge.REQ_PERM || requestCode == MediaBridge.MANAGE_MEDIA_PREP_REQ) && web != null) {
            web.evaluateJavascript("if(window.__permissionChanged){window.__permissionChanged();}", null);
        }
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        if (requestCode == MediaBridge.WRITE_REQ || requestCode == MediaBridge.WRITE_BATCH_REQ) {
            if (bridge != null) bridge.onActivityResult(requestCode, resultCode);
            return;
        }
        if (requestCode == MediaBridge.TRASH_REQ) {
            if (bridge != null) bridge.onTrashResult(resultCode == RESULT_OK);
            return;
        }
        if (requestCode == MediaBridge.DELETE_REQ) {
            if (resultCode == RESULT_OK && web != null) {
                web.evaluateJavascript("if(window.__deleted){window.__deleted();}", null);
            }
            return;
        }
        super.onActivityResult(requestCode, resultCode, data);
    }

    @Override
    protected void onResume() {
        super.onResume();
        if (web != null) {
            web.evaluateJavascript("if(window.__mediaManageChanged){window.__mediaManageChanged();}", null);
        }
    }

    @Override
    protected void onDestroy() {
        if (bridge != null) {
            bridge.destroy();
            bridge = null;
        }
        if (web != null) {
            try {
                web.removeJavascriptInterface("Android");
                web.stopLoading();
                web.destroy();
            } catch (Exception ignored) {}
            web = null;
        }
        super.onDestroy();
    }

    @Override
    public void onBackPressed() {
        if (web != null) {
            web.evaluateJavascript("(function(){try{return window.__back? (window.__back()? 'handled':'exit') : 'exit';}catch(e){return 'exit';}})()", value -> {
                String r = value == null ? "exit" : value.replace("\"", "").trim();
                if (!"handled".equals(r)) {
                    MainActivity.super.onBackPressed();
                }
            });
        } else {
            super.onBackPressed();
        }
    }
}
