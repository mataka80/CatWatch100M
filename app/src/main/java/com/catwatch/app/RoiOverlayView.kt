package com.catwatch.app

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.DashPathEffect
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.util.AttributeSet
import android.view.MotionEvent
import android.view.ScaleGestureDetector
import android.view.View
import kotlin.math.max
import kotlin.math.min

/**
 * 100m 밖 지름 10m 급식소 영역을 지정하는 원형 타겟 포커스 UI (RoiOverlayView)
 * - 초록색 원(Circle) 테두리 + 원 정중앙 카메라 초점 표시(십자선 Crosshair '+' 및 중심점)
 * - 터치/드래그 시 원 중심(normCenterX, normCenterY) 즉시 이동 및 핀치 줌 반지름 조절 지원
 * - 원 바깥 영역을 반투명하게 어둡게 처리하여 타겟 집중도 향상
 */
class RoiOverlayView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null,
    defStyleAttr: Int = 0
) : View(context, attrs, defStyleAttr) {

    /**
     * 원형 ROI 안에 감지된 고양이 바운딩 박스 모델 (정규화 좌표: 0.0f ~ 1.0f, 크롭 정사각형 기준)
     */
    data class DetectedCatBox(
        val normLeft: Float,
        val normTop: Float,
        val normRight: Float,
        val normBottom: Float,
        val score: Float
    )

    // 정규화 중심 좌표 (0.0f ~ 1.0f) 및 정규화 반지름 (화면 폭 대비 비율, 기본값 0.20f = 20%)
    var normCenterX: Float = 0.50f
        private set
    var normCenterY: Float = 0.50f
        private set
    var normRadius: Float = 0.20f
        private set

    // 연속 감지 진행 상태 표시용
    private var consecutiveHits: Int = 0
    private var detectedBoxes: List<DetectedCatBox> = emptyList()

    // 사용자 터치/드래그/핀치 변경 콜백 (SharedPreferences 저장 및 AE/AWB 측광 연동)
    var onRoiChangedListener: ((centerX: Float, centerY: Float, radius: Float) -> Unit)? = null

    private val scrimPath = Path()

    // 원 바깥쪽 어두운 배경 페인트
    private val outsideScrimPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#66000000")
        style = Paint.Style.FILL
    }

    // 지름 10m 구역을 의미하는 초록색 원 테두리 페인트
    private val circleBorderPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#00E676")
        style = Paint.Style.STROKE
        strokeWidth = 6f
    }

    // 정사각형 크롭 가이드 점선 페인트
    private val cropBoxGuidePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#5500E676")
        style = Paint.Style.STROKE
        strokeWidth = 2f
        pathEffect = DashPathEffect(floatArrayOf(10f, 10f), 0f)
    }

    // 중심 십자선(Crosshair '+') 페인트
    private val crosshairPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#00E676")
        style = Paint.Style.STROKE
        strokeWidth = 3.5f
    }

    // 중심 초점 포인트(Center Dot) 페인트
    private val centerDotPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#FF5252")
        style = Paint.Style.FILL
    }

    // 라벨 텍스트 페인트
    private val labelTextPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#00E676")
        textSize = 30f
        isFakeBoldText = true
        setShadowLayer(4f, 0f, 2f, Color.BLACK)
    }

    // 고양이 감지 바운딩 박스 페인트
    private val catBoxPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#FFAB00")
        style = Paint.Style.STROKE
        strokeWidth = 5f
    }

    // 핀치 줌으로 원 반지름 미세 조절 지원
    private val scaleGestureDetector = ScaleGestureDetector(
        context,
        object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(detector: ScaleGestureDetector): Boolean {
                val updatedRadius = (normRadius * detector.scaleFactor).coerceIn(0.05f, 0.45f)
                if (updatedRadius != normRadius) {
                    normRadius = updatedRadius
                    clampCenterToBounds()
                    invalidate()
                    onRoiChangedListener?.invoke(normCenterX, normCenterY, normRadius)
                }
                return true
            }
        }
    )

    /**
     * 초기 저장된 ROI 설정값 복원
     */
    fun setRoiConfig(centerX: Float, centerY: Float, radius: Float, notify: Boolean = false) {
        normRadius = radius.coerceIn(0.05f, 0.45f)
        normCenterX = centerX.coerceIn(0.05f, 0.95f)
        normCenterY = centerY.coerceIn(0.05f, 0.95f)
        clampCenterToBounds()
        invalidate()
        if (notify) {
            onRoiChangedListener?.invoke(normCenterX, normCenterY, normRadius)
        }
    }

    /**
     * 하단 슬라이더로 원 반지름 변경 시 호출
     */
    fun updateRadiusRatio(radiusRatio: Float, notify: Boolean = true) {
        normRadius = radiusRatio.coerceIn(0.05f, 0.45f)
        clampCenterToBounds()
        invalidate()
        if (notify) {
            onRoiChangedListener?.invoke(normCenterX, normCenterY, normRadius)
        }
    }

    /**
     * 실시간 AI 탐지 결과 및 연속 감지 카운트 갱신
     */
    fun updateDetections(boxes: List<DetectedCatBox>, streakCount: Int) {
        detectedBoxes = boxes
        consecutiveHits = streakCount
        // 연속 감지 중일 때 원 테두리 색상을 강조
        circleBorderPaint.color = when {
            streakCount >= 3 -> Color.parseColor("#FF1744")
            streakCount > 0 -> Color.parseColor("#FFD600")
            else -> Color.parseColor("#00E676")
        }
        postInvalidateOnAnimation()
    }

    private fun clampCenterToBounds() {
        val w = width.toFloat()
        val h = height.toFloat()
        if (w <= 0f || h <= 0f) return
        val radiusPx = w * normRadius
        val minX = (radiusPx / w).coerceAtMost(0.5f)
        val maxX = (1f - (radiusPx / w)).coerceAtLeast(0.5f)
        val minY = (radiusPx / h).coerceAtMost(0.5f)
        val maxY = (1f - (radiusPx / h)).coerceAtLeast(0.5f)

        normCenterX = normCenterX.coerceIn(minX, maxX)
        normCenterY = normCenterY.coerceIn(minY, maxY)
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        clampCenterToBounds()
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val viewW = width.toFloat()
        val viewH = height.toFloat()
        if (viewW <= 0f || viewH <= 0f) return

        val cx = viewW * normCenterX
        val cy = viewH * normCenterY
        val radiusPx = min(viewW * normRadius, min(viewW, viewH) * 0.48f)

        // 1. 원 바깥쪽 영역 반투명 암막 처리 (Path.FillType.EVEN_ODD)
        scrimPath.reset()
        scrimPath.fillType = Path.FillType.EVEN_ODD
        scrimPath.addRect(0f, 0f, viewW, viewH, Path.Direction.CW)
        scrimPath.addCircle(cx, cy, radiusPx, Path.Direction.CW)
        canvas.drawPath(scrimPath, outsideScrimPaint)

        // 2. 원형 ROI를 감싸는 정사각형 크롭 바운딩 가이드라인 표시
        val cropRect = RectF(cx - radiusPx, cy - radiusPx, cx + radiusPx, cy + radiusPx)
        canvas.drawRect(cropRect, cropBoxGuidePaint)

        // 3. 지름 10m 구역을 의미하는 초록색 원 테두리 드로잉
        canvas.drawCircle(cx, cy, radiusPx, circleBorderPaint)

        // 4. 원 정중앙 카메라 초점 표시 (십자선 Crosshair '+' 및 중심점)
        val crossArm = max(24f, radiusPx * 0.22f)
        canvas.drawLine(cx - crossArm, cy, cx + crossArm, cy, crosshairPaint)
        canvas.drawLine(cx, cy - crossArm, cx, cy + crossArm, crosshairPaint)
        canvas.drawCircle(cx, cy, 6f, centerDotPaint)

        // 5. 상단 타겟 안내 라벨 드로잉
        val label = if (consecutiveHits > 0) {
            "10m 타겟 ROI (감지 중: ${consecutiveHits}/3초)"
        } else {
            "10m 타겟 ROI (중심: ${(normCenterX * 100).toInt()}%, ${(normCenterY * 100).toInt()}%)"
        }
        val textY = max(40f, cy - radiusPx - 14f)
        canvas.drawText(label, max(16f, cx - radiusPx), textY, labelTextPaint)

        // 6. 원 내부에 감지된 고양이 바운딩 박스 렌더링
        val cropSide = radiusPx * 2f
        for (box in detectedBoxes) {
            val left = cropRect.left + (box.normLeft * cropSide)
            val top = cropRect.top + (box.normTop * cropSide)
            val right = cropRect.left + (box.normRight * cropSide)
            val bottom = cropRect.top + (box.normBottom * cropSide)
            canvas.drawRect(left, top, right, bottom, catBoxPaint)
            val scorePercent = (box.score * 100).toInt()
            canvas.drawText("CAT $scorePercent%", left, max(top - 8f, 24f), labelTextPaint)
        }
    }

    override fun onTouchEvent(event: MotionEvent): Boolean {
        scaleGestureDetector.onTouchEvent(event)
        if (scaleGestureDetector.isInProgress) {
            return true
        }

        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN,
            MotionEvent.ACTION_MOVE -> {
                if (width > 0 && height > 0) {
                    normCenterX = (event.x / width.toFloat()).coerceIn(0.05f, 0.95f)
                    normCenterY = (event.y / height.toFloat()).coerceIn(0.05f, 0.95f)
                    clampCenterToBounds()
                    invalidate()
                    onRoiChangedListener?.invoke(normCenterX, normCenterY, normRadius)
                }
                parent?.requestDisallowInterceptTouchEvent(true)
                return true
            }
            MotionEvent.ACTION_UP,
            MotionEvent.ACTION_CANCEL -> {
                parent?.requestDisallowInterceptTouchEvent(false)
                return true
            }
        }
        return super.onTouchEvent(event)
    }
}
