# PicaPhoto Android

Android WebView 容器与 MediaStore 桥接源码。网页资源在 `app/src/main/assets/www/`，发布前需与仓库根目录 `mobile/` 保持一致。

构建要求：Android SDK Platform 34、Build Tools 34.0.0、JDK 17、Gradle 8.2。

`assembleDebug` 生成 `app/build/outputs/apk/debug/app-debug.apk`。当前版本为 2.0.4（versionCode 54）。

Android 12+ 可在应用内点“申请相册访问权限”进入系统媒体管理特殊访问页；Android 11 会在打开整理大图时一次批量申请当前队列的写入权限。
