package com.catwatch.app

import android.Manifest
import android.annotation.SuppressLint
import android.content.Context
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Matrix
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.hardware.camera2.CaptureRequest
import android.media.AudioAttributes
import android.media.Ringtone
import android.media.RingtoneManager
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.text.InputType
import android.util.Size
import android.view.GestureDetector
import android.view.Gravity
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import androidx.camera.camera2.interop.Camera2Interop
import androidx.camera.core.Camera
import androidx.camera.core.CameraSelector
import androidx.camera.core.FocusMeteringAction
import androidx.camera.core.ImageAnalysis
import androidx.camera.core.ImageProxy
import androidx.camera.core.Preview
import androidx.camera.core.resolutionselector.ResolutionSelector
import androidx.camera.core.resolutionselector.ResolutionStrategy
import androidx.camera.lifecycle.ProcessCameraProvider
import androidx.camera.view.PreviewView
import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat
import androidx.recyclerview.widget.LinearLayoutManager
import androidx.recyclerview.widget.RecyclerView
import okhttp3.Call
import okhttp3.Callback
import okhttp3.MediaType.Companion.toMediaType
import okhttp3.MultipartBody
import okhttp3.OkHttpClient
import okhttp3.Request
import okhttp3.RequestBody.Companion.asRequestBody
import okhttp3.Response
import org.json.JSONArray
import org.json.JSONObject
import org.tensorflow.lite.support.image.TensorImage
import org.tensorflow.lite.task.core.BaseOptions
import org.tensorflow.lite.task.vision.detector.ObjectDetector
import java.io.File
import java.io.FileOutputStream
import java.io.IOException
import java.text.SimpleDateFormat
import java.util.Calendar
import java.util.Date
import java.util.Locale
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt

/**
 * CatWatch 100M (Circular Target UI Edition) - MainActivity
 * - 타겟 기기: Samsung Galaxy Z Flip 3 (SM-F711N, Android 13/14, Min SDK 29, Target SDK 34)
 * - Camera2Interop 수동 무한대 초점(0.0f diopter) 강제 고정 (방충망 및 한글라스 로이복층유리 AF 헌팅 차단)
 * - 1920x1440 이상 고해상도 프레임에서 원형 ROI 정사각형 크롭 + Path.addCircle 원형 마스킹 추론
 * - 1 FPS 발열 제어, "cat" 신뢰도 0.38f 이상, 3초 Debounce, 15분 Cooldown
 * - 08:00 ~ 22:00 자동 스케줄러 (22:00 ~ 08:00 unbindAll 및 알람 원천 차단)
 * - 암막 절전 모드 (화면 밝기 0.01f + 더블 탭 복구)
 * - 로컬 알람음 5초 재생 + OkHttp3 Telegram sendPhoto 멀티파트 비동기 전송
 * - 일일 고양이 개체별 이름 태깅 및 전날 데이터 자동 영구 삭제 (Auto-Purge)
 */
@androidx.camera.camera2.interop.ExperimentalCamera2Interop
class MainActivity : AppCompatActivity() {

    /**
     * 방문 기록 데이터 모델 (VisitRecord)
     */
    data class VisitRecord(
        val id: Long,
        val dateStr: String,
        val timeStr: String,
        var catName: String = "미지정",
        val imagePath: String,
        val confidence: Int
    )

    companion object {
        private const val REQUEST_CAMERA_PERMISSION = 1001
        private const val PREFS_NAME = "catwatch_100m_prefs"

        private const val KEY_ROI_CENTER_X = "roi_center_x"
        private const val KEY_ROI_CENTER_Y = "roi_center_y"
        private const val KEY_ROI_RADIUS = "roi_radius"
        private const val KEY_ZOOM_PROGRESS = "zoom_progress"
        private const val KEY_EXPOSURE_INDEX = "exposure_index"
        private const val KEY_TELEGRAM_TOKEN = "telegram_bot_token"
        private const val KEY_TELEGRAM_CHAT_ID = "telegram_chat_id"
        private const val KEY_VISIT_RECORDS = "visit_records_json"
        private const val KEY_CAT_PRESETS = "cat_presets_json"

        // AI 탐지 및 알람 정책 상수
        private const val ANALYSIS_INTERVAL_MS = 1000L          // 1 FPS (1,000ms 당 1프레임 추론)
        private const val CONFIDENCE_THRESHOLD = 0.38f          // "cat" 최소 신뢰도 0.38f
        private const val DEBOUNCE_REQUIRED_FRAMES = 3          // 연속 3프레임(3초) 체류 필터
        private const val COOLDOWN_DURATION_MS = 900_000L       // 15분(900,000ms) 재알림 방지 쿨다운
        private const val ALARM_RING_DURATION_MS = 5000L        // 로컬 알람음 5초 재생 후 자동 정지

        // 스케줄러 시간 상수 (08:00 ~ 22:00 가동, 22:00 ~ 익일 08:00 완전 정지)
        private const val ACTIVE_START_HOUR = 8
        private const val ACTIVE_END_HOUR = 22
    }

    // UI 뷰 참조
    private lateinit var previewView: PreviewView
    private lateinit var roiOverlayView: RoiOverlayView
    private lateinit var tvScheduleStatus: TextView
    private lateinit var tvDetectionStatus: TextView
    private lateinit var tvRadiusLabel: TextView
    private lateinit var tvZoomLabel: TextView
    private lateinit var tvExposureLabel: TextView
    private lateinit var sbRadius: SeekBar
    private lateinit var sbZoom: SeekBar
    private lateinit var sbExposure: SeekBar
    private lateinit var btnTelegramConfig: Button
    private lateinit var btnTestAlarm: Button
    private lateinit var btnBlackoutMode: Button
    private lateinit var tvDailySummary: TextView
    private lateinit var rvVisitRecords: RecyclerView
    private lateinit var blackScreenOverlay: FrameLayout

    // 데이터 및 상태 관리
    private lateinit var prefs: SharedPreferences
    private val visitList = mutableListOf<VisitRecord>()
    private lateinit var visitAdapter: VisitRecordAdapter

    // CameraX & TFLite & Network
    private var cameraProvider: ProcessCameraProvider? = null
    private var activeCamera: Camera? = null
    private var isCameraBound: Boolean = false
    private var objectDetector: ObjectDetector? = null
    private lateinit var cameraExecutor: ExecutorService

    private val okHttpClient: OkHttpClient by lazy {
        OkHttpClient.Builder()
            .connectTimeout(15, TimeUnit.SECONDS)
            .writeTimeout(20, TimeUnit.SECONDS)
            .readTimeout(20, TimeUnit.SECONDS)
            .build()
    }

    // 추론 스로틀링, Debounce, Cooldown 상태 변수
    @Volatile
    private var lastAnalysisTimestampMs: Long = 0L
    private var consecutiveCatFrames: Int = 0
    private var lastAlarmTriggeredMs: Long = 0L
    private var activeRingtone: Ringtone? = null

    // 메인 스레드 핸들러 (스케줄러, 알람 5초 정지, UI 갱신)
    private val mainHandler = Handler(Looper.getMainLooper())

    // 매분 실행되는 스케줄러 및 전날 데이터 자동 삭제(Auto-Purge) 태스크
    private val scheduleAndPurgeRunnable = object : Runnable {
        override fun run() {
            purgeOldVisitRecords()
            enforceDailySchedule()
            mainHandler.postDelayed(this, 30_000L) // 30초 주기로 정밀 체크 (매분 내 즉시 반영)
        }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        setContentView(R.layout.activity_main)

        prefs = getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
        cameraExecutor = Executors.newSingleThreadExecutor()

        bindViews()
        initObjectDetector()
        setupRoiAndSliders()
        setupActionButtons()
        setupBlackoutDoubleTapRestore()
        setupRecyclerView()

        // 앱 시작 시 전날 데이터 자동 영구 삭제 후 오늘 데이터 로드
        purgeOldVisitRecords()
        loadTodayVisitRecords()

        // 카메라 권한 확인 및 스케줄러 가동
        if (hasCameraPermission()) {
            startCameraProviderInitialization()
        } else {
            ActivityCompat.requestPermissions(
                this,
                arrayOf(Manifest.permission.CAMERA),
                REQUEST_CAMERA_PERMISSION
            )
        }

        mainHandler.post(scheduleAndPurgeRunnable)
    }

    private fun bindViews() {
        previewView = findViewById(R.id.previewView)
        roiOverlayView = findViewById(R.id.roiOverlayView)
        tvScheduleStatus = findViewById(R.id.tvScheduleStatus)
        tvDetectionStatus = findViewById(R.id.tvDetectionStatus)
        tvRadiusLabel = findViewById(R.id.tvRadiusLabel)
        tvZoomLabel = findViewById(R.id.tvZoomLabel)
        tvExposureLabel = findViewById(R.id.tvExposureLabel)
        sbRadius = findViewById(R.id.sbRadius)
        sbZoom = findViewById(R.id.sbZoom)
        sbExposure = findViewById(R.id.sbExposure)
        btnTelegramConfig = findViewById(R.id.btnTelegramConfig)
        btnTestAlarm = findViewById(R.id.btnTestAlarm)
        btnBlackoutMode = findViewById(R.id.btnBlackoutMode)
        tvDailySummary = findViewById(R.id.tvDailySummary)
        rvVisitRecords = findViewById(R.id.rvVisitRecords)
        blackScreenOverlay = findViewById(R.id.blackScreenOverlay)
    }

    /**
     * TensorFlow Lite Task Vision ObjectDetector 초기화 (assets/model.tflite)
     */
    private fun initObjectDetector() {
        try {
            val baseOptions = BaseOptions.builder()
                .setNumThreads(4)
                .build()
            val options = ObjectDetector.ObjectDetectorOptions.builder()
                .setBaseOptions(baseOptions)
                .setScoreThreshold(CONFIDENCE_THRESHOLD)
                .setMaxResults(5)
                .build()
            objectDetector = ObjectDetector.createFromFileAndOptions(this, "model.tflite", options)
        } catch (e: Exception) {
            tvDetectionStatus.text = "⚠️ assets/model.tflite 로드 대기 중 (${e.javaClass.simpleName})"
        }
    }

    /**
     * 원형 타겟 UI (RoiOverlayView) 및 반지름/줌/노출 보정 슬라이더 설정
     */
    private fun setupRoiAndSliders() {
        val savedCenterX = prefs.getFloat(KEY_ROI_CENTER_X, 0.50f)
        val savedCenterY = prefs.getFloat(KEY_ROI_CENTER_Y, 0.50f)
        val savedRadius = prefs.getFloat(KEY_ROI_RADIUS, 0.20f) // 기본값 화면 폭의 20%

        roiOverlayView.setRoiConfig(savedCenterX, savedCenterY, savedRadius, notify = false)

        val initialRadiusPercent = (savedRadius * 100f).roundToInt().coerceIn(5, 45)
        sbRadius.progress = initialRadiusPercent
        tvRadiusLabel.text = "원 반경 (${initialRadiusPercent}%)"

        // 프리뷰 화면 터치/드래그/핀치로 원 중심점 또는 반지름 변경 시 SharedPreferences 저장 및 측광 갱신
        roiOverlayView.onRoiChangedListener = { cx, cy, radius ->
            prefs.edit()
                .putFloat(KEY_ROI_CENTER_X, cx)
                .putFloat(KEY_ROI_CENTER_Y, cy)
                .putFloat(KEY_ROI_RADIUS, radius)
                .apply()

            val pct = (radius * 100f).roundToInt().coerceIn(5, 45)
            if (sbRadius.progress != pct) {
                sbRadius.progress = pct
            }
            tvRadiusLabel.text = "원 반경 (${pct}%)"
            applyCenterMetering(cx, cy)
        }

        // 원 반지름 슬라이더 (5% ~ 45%, 기본 20%)
        sbRadius.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(seekBar: SeekBar?, progress: Int, fromUser: Boolean) {
                val safePct = progress.coerceIn(5, 45)
                tvRadiusLabel.text = "원 반경 (${safePct}%)"
                if (fromUser) {
                    val radiusRatio = safePct / 100f
                    roiOverlayView.updateRadiusRatio(radiusRatio, notify = true)
                }
            }

            override fun onStartTrackingTouch(seekBar: SeekBar?) {}
            override fun onStopTrackingTouch(seekBar: SeekBar?) {}
        })

        // 디지털 줌 슬라이더 (0 ~ 100%)
        val savedZoom = prefs.getInt(KEY_ZOOM_PROGRESS, 0).coerceIn(0, 100)
        sbZoom.progress = savedZoom
        tvZoomLabel.text = "디지털 줌 (${savedZoom}%)"
        sbZoom.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(seekBar: SeekBar?, progress: Int, fromUser: Boolean) {
                tvZoomLabel.text = "디지털 줌 (${progress}%)"
                if (fromUser) {
                    prefs.edit().putInt(KEY_ZOOM_PROGRESS, progress).apply()
                    activeCamera?.cameraControl?.setLinearZoom(progress / 100f)
                }
            }

            override fun onStartTrackingTouch(seekBar: SeekBar?) {}
            override fun onStopTrackingTouch(seekBar: SeekBar?) {}
        })

        // 노출 보정 슬라이더 (AE Compensation Index)
        sbExposure.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(seekBar: SeekBar?, progress: Int, fromUser: Boolean) {
                val cam = activeCamera ?: return
                val state = cam.cameraInfo.exposureState
                if (!state.isExposureCompensationSupported) return
                val range = state.exposureCompensationRange
                val targetIndex = (range.lower + progress).coerceIn(range.lower, range.upper)
                tvExposureLabel.text = "노출 보정 ($targetIndex)"
                if (fromUser) {
                    prefs.edit().putInt(KEY_EXPOSURE_INDEX, targetIndex).apply()
                    cam.cameraControl.setExposureCompensationIndex(targetIndex)
                }
            }

            override fun onStartTrackingTouch(seekBar: SeekBar?) {}
            override fun onStopTrackingTouch(seekBar: SeekBar?) {}
        })
    }

    /**
     * 텔레그램 설정, 테스트 알람, 암막 절전모드 버튼 이벤트 연결
     */
    private fun setupActionButtons() {
        btnTelegramConfig.setOnClickListener {
            showTelegramConfigDialog()
        }

        btnTestAlarm.setOnClickListener {
            triggerTestAlarm()
        }

        btnBlackoutMode.setOnClickListener {
            enterBlackoutPowerSaveMode()
        }
    }

    /**
     * Module 3-2: 유리창 반사 및 OLED 번인 방지용 암막 절전 모드 진입 & 더블 탭 복구
     */
    @SuppressLint("ClickableViewAccessibility")
    private fun setupBlackoutDoubleTapRestore() {
        val gestureDetector = GestureDetector(
            this,
            object : GestureDetector.SimpleOnGestureListener() {
                override fun onDown(e: MotionEvent): Boolean = true

                override fun onDoubleTap(e: MotionEvent): Boolean {
                    exitBlackoutPowerSaveMode()
                    return true
                }
            }
        )

        blackScreenOverlay.setOnTouchListener { _, event ->
            gestureDetector.onTouchEvent(event)
            true
        }
    }

    private fun enterBlackoutPowerSaveMode() {
        blackScreenOverlay.visibility = View.VISIBLE
        val params = window.attributes
        params.screenBrightness = 0.01f // 최저 화면 밝기 (0.01f)
        window.attributes = params
    }

    private fun exitBlackoutPowerSaveMode() {
        blackScreenOverlay.visibility = View.GONE
        val params = window.attributes
        params.screenBrightness = WindowManager.LayoutParams.BRIGHTNESS_OVERRIDE_NONE
        window.attributes = params
        Toast.makeText(this, "암막 절전모드가 해제되었습니다.", Toast.LENGTH_SHORT).show()
    }

    /**
     * Module 3-1: 시간대별 자동 스케줄러 (08:00 ~ 22:00 가동, 22:00 ~ 익일 08:00 완전 슬립)
     */
    private fun isWithinActiveScheduleWindow(): Boolean {
        val now = Calendar.getInstance()
        val hour = now.get(Calendar.HOUR_OF_DAY)
        return hour in ACTIVE_START_HOUR until ACTIVE_END_HOUR
    }

    private fun enforceDailySchedule() {
        if (isWithinActiveScheduleWindow()) {
            tvScheduleStatus.text = "[08:00~22:00 가동 중] 초점: 0.0f (무한대 고정) | 1 FPS 분석"
            tvScheduleStatus.setTextColor(Color.parseColor("#00E676"))
            if (!isCameraBound && cameraProvider != null && hasCameraPermission()) {
                bindCameraUseCases()
            }
        } else {
            // 22:00 ~ 익일 08:00: 즉시 언바인딩 및 슬립 모드 진입 (카메라 및 알람 전면 금지)
            tvScheduleStatus.text = "[22:00~08:00 야간 슬립 모드] 카메라 언바인딩 및 알람 차단됨"
            tvScheduleStatus.setTextColor(Color.parseColor("#FF8A80"))
            tvDetectionStatus.text = "야간 슬립 시간대입니다. 오전 08:00 정각에 자동 재개됩니다."
            consecutiveCatFrames = 0
            roiOverlayView.updateDetections(emptyList(), 0)
            stopAlarmRingtone()
            if (isCameraBound) {
                cameraProvider?.unbindAll()
                activeCamera = null
                isCameraBound = false
            }
        }
    }

    private fun startCameraProviderInitialization() {
        val future = ProcessCameraProvider.getInstance(this)
        future.addListener({
            cameraProvider = future.get()
            enforceDailySchedule()
        }, ContextCompat.getMainExecutor(this))
    }

    /**
     * Module 1-3: CameraX 바인딩 + Camera2Interop 수동 무한대 초점(0.0f) 강제 고정 + 1920x1440 고해상도 분석
     */
    private fun bindCameraUseCases() {
        val provider = cameraProvider ?: return
        if (!isWithinActiveScheduleWindow()) return

        provider.unbindAll()

        // 1. Preview 빌드 및 Camera2Interop 수동 초점 무한대(0.0f diopter) 강제 고정
        val previewBuilder = Preview.Builder()
        val previewInterop = Camera2Interop.Extender(previewBuilder)
        previewInterop.setCaptureRequestOption(
            CaptureRequest.CONTROL_AF_MODE,
            CaptureRequest.CONTROL_AF_MODE_OFF
        )
        previewInterop.setCaptureRequestOption(
            CaptureRequest.LENS_FOCUS_DISTANCE,
            0.0f
        )
        val preview = previewBuilder.build().also {
            it.setSurfaceProvider(previewView.surfaceProvider)
        }

        // 2. ImageAnalysis 빌드 (100m 거리 픽셀 보존을 위해 1920x1440 이상 고해상도 프레임 요청)
        val resolutionSelector = ResolutionSelector.Builder()
            .setResolutionStrategy(
                ResolutionStrategy(
                    Size(1920, 1440),
                    ResolutionStrategy.FALLBACK_RULE_CLOSEST_HIGHER_THEN_LOWER
                )
            )
            .build()

        val imageAnalysisBuilder = ImageAnalysis.Builder()
            .setResolutionSelector(resolutionSelector)
            .setBackpressureStrategy(ImageAnalysis.STRATEGY_KEEP_ONLY_LATEST)
            .setOutputImageFormat(ImageAnalysis.OUTPUT_IMAGE_FORMAT_RGBA_8888)

        val analysisInterop = Camera2Interop.Extender(imageAnalysisBuilder)
        analysisInterop.setCaptureRequestOption(
            CaptureRequest.CONTROL_AF_MODE,
            CaptureRequest.CONTROL_AF_MODE_OFF
        )
        analysisInterop.setCaptureRequestOption(
            CaptureRequest.LENS_FOCUS_DISTANCE,
            0.0f
        )

        val imageAnalysis = imageAnalysisBuilder.build().also { analysis ->
            analysis.setAnalyzer(cameraExecutor) { imageProxy ->
                processFrame(imageProxy)
            }
        }

        try {
            activeCamera = provider.bindToLifecycle(
                this,
                CameraSelector.DEFAULT_BACK_CAMERA,
                preview,
                imageAnalysis
            )
            isCameraBound = true
            restoreCameraControlsAndMetering()
        } catch (e: Exception) {
            isCameraBound = false
            tvDetectionStatus.text = "카메라 바인딩 오류: ${e.localizedMessage}"
        }
    }

    /**
     * 줌, 노출 보정 복원 및 원 중심 좌표 기준 측광(AE/AWB MeteringPoint) 적용
     */
    private fun restoreCameraControlsAndMetering() {
        val cam = activeCamera ?: return

        // 디지털 줌 복원
        val savedZoom = prefs.getInt(KEY_ZOOM_PROGRESS, 0).coerceIn(0, 100)
        cam.cameraControl.setLinearZoom(savedZoom / 100f)

        // 노출 보정 범위 설정 및 복원
        val exposureState = cam.cameraInfo.exposureState
        if (exposureState.isExposureCompensationSupported) {
            val range = exposureState.exposureCompensationRange
            val totalSteps = range.upper - range.lower
            sbExposure.max = totalSteps
            val savedExp = prefs.getInt(KEY_EXPOSURE_INDEX, 0).coerceIn(range.lower, range.upper)
            sbExposure.progress = savedExp - range.lower
            tvExposureLabel.text = "노출 보정 ($savedExp)"
            cam.cameraControl.setExposureCompensationIndex(savedExp)
        } else {
            sbExposure.isEnabled = false
            tvExposureLabel.text = "노출 보정 (미지원)"
        }

        // 원의 중심 좌표(centerX, centerY)를 기준으로 AE/AWB 측광 연동
        applyCenterMetering(roiOverlayView.normCenterX, roiOverlayView.normCenterY)
    }

    /**
     * 원형 ROI 중심 좌표를 기준으로 AE/AWB 측광(MeteringPoint) 수행 (AF는 수동 0.0f 유지를 위해 제외)
     */
    private fun applyCenterMetering(normX: Float, normY: Float) {
        val cam = activeCamera ?: return
        if (previewView.width <= 0 || previewView.height <= 0) return

        val factory = previewView.meteringPointFactory
        val point = factory.createPoint(
            normX * previewView.width,
            normY * previewView.height
        )
        val action = FocusMeteringAction.Builder(
            point,
            FocusMeteringAction.FLAG_AE or FocusMeteringAction.FLAG_AWB
        )
            .setAutoCancelDuration(5, TimeUnit.SECONDS)
            .build()
        cam.cameraControl.startFocusAndMetering(action)
    }

    /**
     * Module 1-2 & Module 2:
     * 1) 1,000ms(1 FPS) 발열 제어 스로틀링
     * 2) 1920x1440 이상 원본 프레임 회전 정렬 후 원형 ROI를 감싸는 정사각형 바운딩 영역(centerX - r, centerY - r, 2r x 2r) 원본 픽셀 크롭
     * 3) 잘라낸 정사각형 비트맵에서 원 바깥쪽 모서리 영역을 검은색으로 마스킹(Path.addCircle + Path.FillType.INVERSE_WINDING)
     * 4) TFLite ObjectDetector 추론 ("cat" & confidence >= 0.38f)
     * 5) 연속 3프레임(3초) Debounce 및 15분 Cooldown 처리
     */
    private fun processFrame(imageProxy: ImageProxy) {
        try {
            // 야간 슬립 시간대(22:00 ~ 08:00)에는 즉시 프레임 폐기
            if (!isWithinActiveScheduleWindow()) {
                return
            }

            // 1 FPS (1,000ms) 스로틀링 체크
            val nowElapsed = SystemClock.elapsedRealtime()
            if (nowElapsed - lastAnalysisTimestampMs < ANALYSIS_INTERVAL_MS) {
                return
            }
            lastAnalysisTimestampMs = nowElapsed

            // RGBA_8888 ImageProxy -> 원본 고해상도 Bitmap 변환 및 센서 회전 보정
            val rawBitmap = imageProxyToUprightBitmap(imageProxy) ?: return

            // 정규화 ROI 좌표 및 반지름 가져오기
            val normCx = roiOverlayView.normCenterX
            val normCy = roiOverlayView.normCenterY
            val normR = roiOverlayView.normRadius

            val frameW = rawBitmap.width
            val frameH = rawBitmap.height

            // 원본 프레임 상의 원 중심 및 반지름(픽셀) 계산
            val centerX = (frameW * normCx).roundToInt()
            val centerY = (frameH * normCy).roundToInt()
            val maxAllowedR = min(frameW, frameH) / 2
            val radiusPx = (frameW * normR).roundToInt().coerceIn(32, maxAllowedR)

            // 원을 감싸는 정사각형 바운딩 영역(centerX - r, centerY - r, 가로세로 2r) 경계 보정
            val side = radiusPx * 2
            val cropLeft = (centerX - radiusPx).coerceIn(0, max(0, frameW - side))
            val cropTop = (centerY - radiusPx).coerceIn(0, max(0, frameH - side))
            val actualSide = min(side, min(frameW - cropLeft, frameH - cropTop))

            if (actualSide <= 16) return

            // 1. 원본 픽셀 그대로 정사각형 크롭(Crop)
            val squareCroppedBitmap = Bitmap.createBitmap(
                rawBitmap,
                cropLeft,
                cropTop,
                actualSide,
                actualSide
            )

            // 2. 원형 마스킹(Circular Masking): 원 바깥쪽 모서리 영역을 검은색(#000000)으로 마스킹
            val maskedCircularBitmap = applyCircularBlackMask(squareCroppedBitmap)

            // 3. TFLite ObjectDetector 추론 수행
            val detector = objectDetector
            val matchedCats = mutableListOf<RoiOverlayView.DetectedCatBox>()
            var highestConfidence = 0f

            if (detector != null) {
                val tensorImage = TensorImage.fromBitmap(maskedCircularBitmap)
                val results = detector.detect(tensorImage)

                for (detection in results) {
                    val category = detection.categories.firstOrNull { cat ->
                        cat.label.trim().equals("cat", ignoreCase = true) &&
                            cat.score >= CONFIDENCE_THRESHOLD
                    }
                    if (category != null) {
                        val box = detection.boundingBox
                        val sideF = actualSide.toFloat()
                        matchedCats.add(
                            RoiOverlayView.DetectedCatBox(
                                normLeft = (box.left / sideF).coerceIn(0f, 1f),
                                normTop = (box.top / sideF).coerceIn(0f, 1f),
                                normRight = (box.right / sideF).coerceIn(0f, 1f),
                                normBottom = (box.bottom / sideF).coerceIn(0f, 1f),
                                score = category.score
                            )
                        )
                        if (category.score > highestConfidence) {
                            highestConfidence = category.score
                        }
                    }
                }
            }

            // 4. Debounce (연속 3프레임 = 3초 이상 감지 필터) 처리
            if (matchedCats.isNotEmpty()) {
                consecutiveCatFrames++
            } else {
                consecutiveCatFrames = 0
            }

            val currentStreak = consecutiveCatFrames
            val confidencePercent = (highestConfidence * 100f).roundToInt()

            // 연속 3프레임 도달 시 출현 이벤트 트리거
            var annotatedSnapshotForEvent: Bitmap? = null
            if (currentStreak == DEBOUNCE_REQUIRED_FRAMES) {
                annotatedSnapshotForEvent = drawAnnotatedSnapshot(
                    maskedCircularBitmap,
                    matchedCats,
                    confidencePercent
                )
            }

            mainHandler.post {
                roiOverlayView.updateDetections(matchedCats, currentStreak)
                if (matchedCats.isNotEmpty()) {
                    tvDetectionStatus.text =
                        "🐱 원형 타겟 내 고양이 감지! 신뢰도 ${confidencePercent}% (연속 ${currentStreak}/${DEBOUNCE_REQUIRED_FRAMES}초)"
                } else {
                    tvDetectionStatus.text =
                        "감시 중 (해상도: ${frameW}x${frameH}, 크롭: ${actualSide}x${actualSide}px)"
                }

                if (annotatedSnapshotForEvent != null) {
                    handleConfirmedCatAppearance(annotatedSnapshotForEvent, confidencePercent)
                }
            }
        } catch (e: Exception) {
            mainHandler.post {
                tvDetectionStatus.text = "프레임 분석 예외: ${e.localizedMessage}"
            }
        } finally {
            imageProxy.close()
        }
    }

    /**
     * ImageProxy(RGBA_8888)를 센서 회전 각도가 반영된 정방향 Bitmap으로 변환
     */
    private fun imageProxyToUprightBitmap(imageProxy: ImageProxy): Bitmap? {
        val plane = imageProxy.planes.firstOrNull() ?: return null
        val buffer = plane.buffer
        buffer.rewind()

        val width = imageProxy.width
        val height = imageProxy.height
        val pixelStride = plane.pixelStride
        val rowStride = plane.rowStride
        val rowPadding = rowStride - pixelStride * width

        val strideWidth = width + rowPadding / pixelStride
        val argbBitmap = Bitmap.createBitmap(strideWidth, height, Bitmap.Config.ARGB_8888)
        argbBitmap.copyPixelsFromBuffer(buffer)

        val rotationDegrees = imageProxy.imageInfo.rotationDegrees
        val matrix = Matrix().apply {
            if (rotationDegrees != 0) {
                postRotate(rotationDegrees.toFloat())
            }
        }

        return Bitmap.createBitmap(argbBitmap, 0, 0, width, height, matrix, true)
    }

    /**
     * 정사각형 크롭 비트맵에서 원 바깥쪽 모서리 영역을 검은색(#000000)으로 마스킹 (Path.addCircle 활용)
     */
    private fun applyCircularBlackMask(squareBitmap: Bitmap): Bitmap {
        val size = squareBitmap.width
        val output = squareBitmap.copy(Bitmap.Config.ARGB_8888, true)
        val canvas = Canvas(output)

        val cx = size / 2f
        val cy = size / 2f
        val radius = size / 2f

        val outsideMaskPath = Path().apply {
            fillType = Path.FillType.INVERSE_WINDING
            addCircle(cx, cy, radius, Path.Direction.CW)
        }

        val blackMaskPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            color = Color.BLACK
            style = Paint.Style.FILL
        }

        // 원 바깥쪽 모서리 영역을 검은색으로 칠함
        canvas.drawPath(outsideMaskPath, blackMaskPaint)
        return output
    }

    /**
     * 고양이 출현 확정 시 스냅샷에 원형 테두리, 중심 초점 십자선('+'), 바운딩 박스를 그려서 반환
     */
    private fun drawAnnotatedSnapshot(
        baseBitmap: Bitmap,
        boxes: List<RoiOverlayView.DetectedCatBox>,
        confidencePercent: Int
    ): Bitmap {
        val result = baseBitmap.copy(Bitmap.Config.ARGB_8888, true)
        val canvas = Canvas(result)
        val side = result.width.toFloat()
        val half = side / 2f

        // 1. 초록색 원형 타겟 테두리
        val circlePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            color = Color.parseColor("#00E676")
            style = Paint.Style.STROKE
            strokeWidth = max(3f, side * 0.01f)
        }
        canvas.drawCircle(half, half, half - circlePaint.strokeWidth, circlePaint)

        // 2. 중심 십자선(Crosshair '+') 마크
        val crossArm = max(16f, side * 0.06f)
        canvas.drawLine(half - crossArm, half, half + crossArm, half, circlePaint)
        canvas.drawLine(half, half - crossArm, half, half + crossArm, circlePaint)

        // 3. 고양이 감지 바운딩 박스 및 신뢰도 텍스트
        val boxPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            color = Color.parseColor("#FFAB00")
            style = Paint.Style.STROKE
            strokeWidth = max(4f, side * 0.012f)
        }
        val textPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            color = Color.parseColor("#FFAB00")
            textSize = max(22f, side * 0.055f)
            isFakeBoldText = true
            setShadowLayer(4f, 0f, 2f, Color.BLACK)
        }

        for (box in boxes) {
            val rect = RectF(
                box.normLeft * side,
                box.normTop * side,
                box.normRight * side,
                box.normBottom * side
            )
            canvas.drawRect(rect, boxPaint)
            canvas.drawText(
                "CAT ${(box.score * 100).roundToInt()}%",
                rect.left + 6f,
                max(rect.top - 8f, textPaint.textSize + 4f),
                textPaint
            )
        }

        if (boxes.isEmpty()) {
            canvas.drawText("TEST SNAPSHOT ($confidencePercent%)", 16f, side - 20f, textPaint)
        }

        return result
    }

    /**
     * Module 2-2 & Module 4 & Module 5:
     * 고양이 출현 확정 시 로컬 저장소(filesDir) 스냅샷 기록 추가 + 15분 Cooldown 체크 후 벨소리 & 텔레그램 발송
     */
    private fun handleConfirmedCatAppearance(annotatedBitmap: Bitmap, confidencePercent: Int) {
        if (!isWithinActiveScheduleWindow()) return

        val now = Date()
        val dateStr = SimpleDateFormat("yyyy-MM-dd", Locale.KOREA).format(now)
        val timeStr = SimpleDateFormat("HH:mm:ss", Locale.KOREA).format(now)
        val recordId = System.currentTimeMillis()

        // 1. 스냅샷 JPG를 내부 저장소(filesDir)에 저장
        val snapshotFile = File(filesDir, "cat_${dateStr}_${recordId}.jpg")
        try {
            FileOutputStream(snapshotFile).use { fos ->
                annotatedBitmap.compress(Bitmap.CompressFormat.JPEG, 90, fos)
                fos.flush()
            }
        } catch (e: Exception) {
            Toast.makeText(this, "스냅샷 저장 실패: ${e.localizedMessage}", Toast.LENGTH_SHORT).show()
            return
        }

        // 2. 방문 기록(VisitRecord) 생성 및 리스트/SharedPreferences 반영 (쿨다운 중에도 기록은 항상 남김)
        val newRecord = VisitRecord(
            id = recordId,
            dateStr = dateStr,
            timeStr = timeStr,
            catName = "미지정",
            imagePath = snapshotFile.absolutePath,
            confidence = confidencePercent
        )
        visitList.add(0, newRecord)
        saveVisitRecordsToPrefs()
        visitAdapter.notifyItemInserted(0)
        rvVisitRecords.scrollToPosition(0)
        updateDailySummaryHeader()

        // 3. 15분(900,000ms) Cooldown 확인
        val nowElapsed = SystemClock.elapsedRealtime()
        val isCooldownActive = lastAlarmTriggeredMs > 0L &&
            (nowElapsed - lastAlarmTriggeredMs < COOLDOWN_DURATION_MS)

        if (isCooldownActive) {
            val remainMin = ((COOLDOWN_DURATION_MS - (nowElapsed - lastAlarmTriggeredMs)) / 60000L) + 1
            tvDetectionStatus.text =
                "🐱 방문 기록 저장됨 ($timeStr) | 쿨다운 중 (알람/텔레그램 생략, 약 ${remainMin}분 남음)"
            return
        }

        // 4. 쿨다운이 아닐 경우 로컬 5초 알람음 재생 + 텔레그램 사진 전송
        lastAlarmTriggeredMs = nowElapsed
        playLocalAlarmForFiveSeconds()
        sendTelegramPhotoAsync(snapshotFile, timeStr, confidencePercent)
    }

    /**
     * 즉시 테스트할 수 있는 [테스트 알람] 실행
     */
    private fun triggerTestAlarm() {
        val testBmp = Bitmap.createBitmap(480, 480, Bitmap.Config.ARGB_8888)
        val canvas = Canvas(testBmp)
        canvas.drawColor(Color.parseColor("#1B262C"))

        val sampleBox = listOf(
            RoiOverlayView.DetectedCatBox(0.28f, 0.28f, 0.72f, 0.72f, 0.92f)
        )
        val annotated = drawAnnotatedSnapshot(testBmp, sampleBox, 92)
        val timeStr = SimpleDateFormat("HH:mm:ss", Locale.KOREA).format(Date())
        val tempFile = File(filesDir, "cat_test_${System.currentTimeMillis()}.jpg")

        try {
            FileOutputStream(tempFile).use { fos ->
                annotated.compress(Bitmap.CompressFormat.JPEG, 90, fos)
                fos.flush()
            }
        } catch (e: Exception) {
            Toast.makeText(this, "테스트 이미지 생성 오류: ${e.localizedMessage}", Toast.LENGTH_SHORT).show()
            return
        }

        playLocalAlarmForFiveSeconds()
        sendTelegramPhotoAsync(tempFile, timeStr, 92, isTest = true)
    }

    /**
     * Module 4-1: 공기계 자체 벨소리 (RingtoneManager.TYPE_ALARM & AudioAttributes.USAGE_ALARM 5초 재생 후 자동 정지)
     */
    private fun playLocalAlarmForFiveSeconds() {
        if (!isWithinActiveScheduleWindow()) return

        stopAlarmRingtone()
        try {
            val alarmUri = RingtoneManager.getDefaultUri(RingtoneManager.TYPE_ALARM)
                ?: RingtoneManager.getDefaultUri(RingtoneManager.TYPE_NOTIFICATION)
                ?: RingtoneManager.getDefaultUri(RingtoneManager.TYPE_RINGTONE)

            val ringtone = RingtoneManager.getRingtone(applicationContext, alarmUri)
            ringtone.audioAttributes = AudioAttributes.Builder()
                .setUsage(AudioAttributes.USAGE_ALARM)
                .setContentType(AudioAttributes.CONTENT_TYPE_SONIFICATION)
                .build()
            ringtone.play()
            activeRingtone = ringtone

            // 5초 후 자동 정지
            mainHandler.postDelayed({
                stopAlarmRingtone()
            }, ALARM_RING_DURATION_MS)
        } catch (e: Exception) {
            Toast.makeText(this, "벨소리 재생 실패: ${e.localizedMessage}", Toast.LENGTH_SHORT).show()
        }
    }

    private fun stopAlarmRingtone() {
        try {
            activeRingtone?.let {
                if (it.isPlaying) {
                    it.stop()
                }
            }
        } catch (_: Exception) {
        } finally {
            activeRingtone = null
        }
    }

    /**
     * Module 4-2: Telegram Bot API 연동 (OkHttp3 비동기 멀티파트 전송)
     * 캡션 포맷: "🐱 [고양이 출현] HH:mm:ss 급식소 대기 중 (신뢰도 XX%)"
     */
    private fun sendTelegramPhotoAsync(
        photoFile: File,
        timeStr: String,
        confidencePercent: Int,
        isTest: Boolean = false
    ) {
        val botToken = prefs.getString(KEY_TELEGRAM_TOKEN, "")?.trim().orEmpty()
        val chatId = prefs.getString(KEY_TELEGRAM_CHAT_ID, "")?.trim().orEmpty()

        if (botToken.isEmpty() || chatId.isEmpty()) {
            Toast.makeText(
                this,
                "텔레그램 Bot Token 또는 Chat ID가 설정되지 않았습니다.",
                Toast.LENGTH_SHORT
            ).show()
            if (isTest) photoFile.delete()
            return
        }

        val caption = "🐱 [고양이 출현] $timeStr 급식소 대기 중 (신뢰도 ${confidencePercent}%)"
        val url = "https://api.telegram.org/bot${botToken}/sendPhoto"

        val requestBody = MultipartBody.Builder()
            .setType(MultipartBody.FORM)
            .addFormDataPart("chat_id", chatId)
            .addFormDataPart("caption", caption)
            .addFormDataPart(
                "photo",
                photoFile.name,
                photoFile.asRequestBody("image/jpeg".toMediaType())
            )
            .build()

        val request = Request.Builder()
            .url(url)
            .post(requestBody)
            .build()

        okHttpClient.newCall(request).enqueue(object : Callback {
            override fun onFailure(call: Call, e: IOException) {
                if (isTest) photoFile.delete()
                mainHandler.post {
                    Toast.makeText(
                        this@MainActivity,
                        "텔레그램 전송 실패: ${e.localizedMessage}",
                        Toast.LENGTH_SHORT
                    ).show()
                }
            }

            override fun onResponse(call: Call, response: Response) {
                val success = response.isSuccessful
                val code = response.code
                response.close()
                if (isTest) photoFile.delete()
                mainHandler.post {
                    if (success) {
                        Toast.makeText(
                            this@MainActivity,
                            "텔레그램 알림 사진 전송 완료!",
                            Toast.LENGTH_SHORT
                        ).show()
                    } else {
                        Toast.makeText(
                            this@MainActivity,
                            "텔레그램 API 응답 오류 (HTTP $code)",
                            Toast.LENGTH_SHORT
                        ).show()
                    }
                }
            }
        })
    }

    /**
     * 텔레그램 Bot Token 및 Chat ID 설정 다이얼로그
     */
    private fun showTelegramConfigDialog() {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            val pad = (20 * resources.displayMetrics.density).toInt()
            setPadding(pad, pad, pad, pad)
        }

        val etToken = EditText(this).apply {
            hint = "Bot Token (예: 123456789:AAH...)"
            inputType = InputType.TYPE_CLASS_TEXT
            setText(prefs.getString(KEY_TELEGRAM_TOKEN, ""))
        }

        val etChatId = EditText(this).apply {
            hint = "Chat ID (예: 987654321 또는 -100...)"
            inputType = InputType.TYPE_CLASS_TEXT
            setText(prefs.getString(KEY_TELEGRAM_CHAT_ID, ""))
        }

        container.addView(etToken)
        container.addView(etChatId)

        AlertDialog.Builder(this)
            .setTitle("Telegram Bot API 설정")
            .setView(container)
            .setPositiveButton("저장") { _, _ ->
                prefs.edit()
                    .putString(KEY_TELEGRAM_TOKEN, etToken.text.toString().trim())
                    .putString(KEY_TELEGRAM_CHAT_ID, etChatId.text.toString().trim())
                    .apply()
                Toast.makeText(this, "텔레그램 설정이 저장되었습니다.", Toast.LENGTH_SHORT).show()
            }
            .setNegativeButton("취소", null)
            .show()
    }

    /**
     * Module 5: 일일 고양이 개체별 이름 태깅 및 전날 데이터 자동 영구 삭제 (Auto-Purge)
     */
    private fun getTodayDateString(): String {
        return SimpleDateFormat("yyyy-MM-dd", Locale.KOREA).format(Date())
    }

    private fun purgeOldVisitRecords() {
        val todayStr = getTodayDateString()
        val rawJson = prefs.getString(KEY_VISIT_RECORDS, "[]") ?: "[]"
        val keptArray = JSONArray()
        var deletedCount = 0

        try {
            val array = JSONArray(rawJson)
            for (i in 0 until array.length()) {
                val obj = array.getJSONObject(i)
                val recordDate = obj.optString("dateStr", "")
                val imagePath = obj.optString("imagePath", "")
                if (recordDate == todayStr) {
                    keptArray.put(obj)
                } else {
                    if (imagePath.isNotEmpty()) {
                        val file = File(imagePath)
                        if (file.exists()) {
                            file.delete()
                        }
                    }
                    deletedCount++
                }
            }
        } catch (_: Exception) {
        }

        // filesDir 내부에 남아있는 전날 스냅샷 파일도 안전하게 정리
        filesDir.listFiles()?.forEach { file ->
            if (file.name.startsWith("cat_") && !file.name.contains(todayStr)) {
                file.delete()
            }
        }

        if (deletedCount > 0) {
            prefs.edit().putString(KEY_VISIT_RECORDS, keptArray.toString()).apply()
            val iterator = visitList.iterator()
            var listChanged = false
            while (iterator.hasNext()) {
                val item = iterator.next()
                if (item.dateStr != todayStr) {
                    iterator.remove()
                    listChanged = true
                }
            }
            if (listChanged && ::visitAdapter.isInitialized) {
                visitAdapter.notifyDataSetChanged()
                updateDailySummaryHeader()
            }
        }
    }

    private fun loadTodayVisitRecords() {
        visitList.clear()
        val todayStr = getTodayDateString()
        val rawJson = prefs.getString(KEY_VISIT_RECORDS, "[]") ?: "[]"

        try {
            val array = JSONArray(rawJson)
            for (i in 0 until array.length()) {
                val obj = array.getJSONObject(i)
                val dateStr = obj.optString("dateStr", "")
                if (dateStr == todayStr) {
                    visitList.add(
                        VisitRecord(
                            id = obj.optLong("id", System.currentTimeMillis()),
                            dateStr = dateStr,
                            timeStr = obj.optString("timeStr", "00:00:00"),
                            catName = obj.optString("catName", "미지정"),
                            imagePath = obj.optString("imagePath", ""),
                            confidence = obj.optInt("confidence", 0)
                        )
                    )
                }
            }
        } catch (_: Exception) {
        }

        visitAdapter.notifyDataSetChanged()
        updateDailySummaryHeader()
    }

    private fun saveVisitRecordsToPrefs() {
        val array = JSONArray()
        for (record in visitList) {
            val obj = JSONObject().apply {
                put("id", record.id)
                put("dateStr", record.dateStr)
                put("timeStr", record.timeStr)
                put("catName", record.catName)
                put("imagePath", record.imagePath)
                put("confidence", record.confidence)
            }
            array.put(obj)
        }
        prefs.edit().putString(KEY_VISIT_RECORDS, array.toString()).apply()
    }

    /**
     * 기본 프리셋(["치즈", "삼색이", "턱시도", "고등어", "까망이"]) + 사용자 추가 프리셋 불러오기
     */
    private fun loadCatNamePresets(): MutableList<String> {
        val defaults = listOf("치즈", "삼색이", "턱시도", "고등어", "까망이")
        val savedJson = prefs.getString(KEY_CAT_PRESETS, null) ?: return defaults.toMutableList()
        val result = mutableListOf<String>()
        try {
            val arr = JSONArray(savedJson)
            for (i in 0 until arr.length()) {
                val name = arr.optString(i).trim()
                if (name.isNotEmpty() && !result.contains(name)) {
                    result.add(name)
                }
            }
        } catch (_: Exception) {
        }
        for (d in defaults) {
            if (!result.contains(d)) {
                result.add(0, d)
            }
        }
        return result
    }

    private fun saveCatNamePresets(presets: List<String>) {
        val arr = JSONArray()
        presets.forEach { arr.put(it) }
        prefs.edit().putString(KEY_CAT_PRESETS, arr.toString()).apply()
    }

    /**
     * 리스트 항목 클릭 시 개체별 이름 태깅 다이얼로그 표시
     */
    private fun showCatNameTagDialog(position: Int) {
        if (position !in visitList.indices) return
        val record = visitList[position]
        val presets = loadCatNamePresets()
        val addCustomOption = "+ 새 고양이 이름 직접 입력"
        val dialogItems = (presets + addCustomOption).toTypedArray()

        AlertDialog.Builder(this)
            .setTitle("방문 고양이 이름 태깅 (${record.timeStr})")
            .setItems(dialogItems) { _, which ->
                if (which == dialogItems.lastIndex) {
                    showAddCustomCatNameDialog(position, presets)
                } else {
                    record.catName = presets[which]
                    saveVisitRecordsToPrefs()
                    visitAdapter.notifyItemChanged(position)
                    updateDailySummaryHeader()
                }
            }
            .setNegativeButton("닫기", null)
            .show()
    }

    private fun showAddCustomCatNameDialog(position: Int, currentPresets: MutableList<String>) {
        if (position !in visitList.indices) return
        val input = EditText(this).apply {
            hint = "새 고양이 이름 입력 (예: 노랑이)"
            inputType = InputType.TYPE_CLASS_TEXT
        }
        val container = FrameLayout(this).apply {
            val pad = (20 * resources.displayMetrics.density).toInt()
            setPadding(pad, pad / 2, pad, 0)
            addView(input)
        }

        AlertDialog.Builder(this)
            .setTitle("새 고양이 이름 등록")
            .setView(container)
            .setPositiveButton("저장") { _, _ ->
                val newName = input.text.toString().trim()
                if (newName.isNotEmpty()) {
                    if (!currentPresets.contains(newName)) {
                        currentPresets.add(newName)
                        saveCatNamePresets(currentPresets)
                    }
                    visitList[position].catName = newName
                    saveVisitRecordsToPrefs()
                    visitAdapter.notifyItemChanged(position)
                    updateDailySummaryHeader()
                }
            }
            .setNegativeButton("취소", null)
            .show()
    }

    /**
     * 리스트 상단에 오늘 개체별 누적 방문 횟수 요약 표시
     * 포맷 예시: "오늘 방문(총 3회): 치즈 2회 / 삼색이 1회"
     */
    private fun updateDailySummaryHeader() {
        val total = visitList.size
        if (total == 0) {
            tvDailySummary.text = "오늘 방문(총 0회): 기록 없음"
            return
        }
        val groupedCounts = linkedMapOf<String, Int>()
        for (item in visitList) {
            groupedCounts[item.catName] = (groupedCounts[item.catName] ?: 0) + 1
        }
        val breakdown = groupedCounts.entries.joinToString(" / ") { "${it.key} ${it.value}회" }
        tvDailySummary.text = "오늘 방문(총 ${total}회): $breakdown"
    }

    private fun setupRecyclerView() {
        visitAdapter = VisitRecordAdapter(visitList) { clickedPos ->
            showCatNameTagDialog(clickedPos)
        }
        rvVisitRecords.layoutManager = LinearLayoutManager(this)
        rvVisitRecords.adapter = visitAdapter
    }

    /**
     * 오늘 촬영된 스냅샷 썸네일, 방문 시각, 고양이 이름을 표시하는 RecyclerView 어댑터
     */
    inner class VisitRecordAdapter(
        private val items: List<VisitRecord>,
        private val onItemClick: (Int) -> Unit
    ) : RecyclerView.Adapter<VisitRecordAdapter.VisitViewHolder>() {

        inner class VisitViewHolder(
            val rootLayout: LinearLayout,
            val ivThumb: ImageView,
            val tvTitle: TextView,
            val tvSub: TextView,
            val tvTagBadge: TextView
        ) : RecyclerView.ViewHolder(rootLayout)

        override fun onCreateViewHolder(parent: ViewGroup, viewType: Int): VisitViewHolder {
            val density = parent.resources.displayMetrics.density
            val root = LinearLayout(parent.context).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                setBackgroundColor(Color.parseColor("#292929"))
                val pad = (8 * density).toInt()
                setPadding(pad, pad, pad, pad)
                layoutParams = RecyclerView.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT
                ).apply {
                    bottomMargin = (6 * density).toInt()
                }
            }

            val thumbSize = (54 * density).toInt()
            val ivThumb = ImageView(parent.context).apply {
                layoutParams = LinearLayout.LayoutParams(thumbSize, thumbSize).apply {
                    marginEnd = (10 * density).toInt()
                }
                scaleType = ImageView.ScaleType.CENTER_CROP
                setBackgroundColor(Color.BLACK)
            }

            val textContainer = LinearLayout(parent.context).apply {
                orientation = LinearLayout.VERTICAL
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            }

            val tvTitle = TextView(parent.context).apply {
                setTextColor(Color.WHITE)
                textSize = 13f
                paint.isFakeBoldText = true
            }

            val tvSub = TextView(parent.context).apply {
                setTextColor(Color.parseColor("#B0BEC5"))
                textSize = 11f
            }

            textContainer.addView(tvTitle)
            textContainer.addView(tvSub)

            val tvTagBadge = TextView(parent.context).apply {
                setTextColor(Color.parseColor("#121212"))
                setBackgroundColor(Color.parseColor("#00E676"))
                textSize = 11f
                paint.isFakeBoldText = true
                val hPad = (10 * density).toInt()
                val vPad = (5 * density).toInt()
                setPadding(hPad, vPad, hPad, vPad)
            }

            root.addView(ivThumb)
            root.addView(textContainer)
            root.addView(tvTagBadge)

            return VisitViewHolder(root, ivThumb, tvTitle, tvSub, tvTagBadge)
        }

        override fun onBindViewHolder(holder: VisitViewHolder, position: Int) {
            val item = items[position]
            holder.tvTitle.text = "🐱 ${item.catName} (방문 시각: ${item.timeStr})"
            holder.tvSub.text = "탐지 신뢰도: ${item.confidence}% | 터치하여 이름 변경"
            holder.tvTagBadge.text = item.catName

            val imgFile = File(item.imagePath)
            if (imgFile.exists()) {
                val bmp = BitmapFactory.decodeFile(imgFile.absolutePath)
                holder.ivThumb.setImageBitmap(bmp)
            } else {
                holder.ivThumb.setImageDrawable(null)
            }

            holder.rootLayout.setOnClickListener {
                val adapterPos = holder.bindingAdapterPosition
                if (adapterPos != RecyclerView.NO_POSITION) {
                    onItemClick(adapterPos)
                }
            }
        }

        override fun getItemCount(): Int = items.size
    }

    private fun hasCameraPermission(): Boolean {
        return ContextCompat.checkSelfPermission(
            this,
            Manifest.permission.CAMERA
        ) == PackageManager.PERMISSION_GRANTED
    }

    override fun onRequestPermissionsResult(
        requestCode: Int,
        permissions: Array<out String>,
        grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQUEST_CAMERA_PERMISSION) {
            if (grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
                startCameraProviderInitialization()
            } else {
                Toast.makeText(this, "고양이 탐지를 위해 카메라 권한이 필요합니다.", Toast.LENGTH_LONG).show()
            }
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        mainHandler.removeCallbacksAndMessages(null)
        stopAlarmRingtone()
        cameraExecutor.shutdown()
        objectDetector?.close()
    }
}