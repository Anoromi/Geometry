import Mathlib.Tactic
import Geometry.Basic
import Geometry.Triangle
import Geometry.Congruence

noncomputable section
structure Quadrilateral where
  point1: Point
  point2: Point
  point3: Point
  point4: Point
  same_plane: ∃ pl: Plane, point1 ∈ pl ∧ point2 ∈ pl ∧ point3 ∈ pl ∧ point4 ∈ pl


  ne_1: let h : Set Point := {point2, point3, point4}; point1 ∉ h
  ne_2: let h : Set Point := {point1, point3, point4}; point2 ∉ h
  ne_3: let h : Set Point := {point1, point2, point4}; point3 ∉ h
  ne_4: let h : Set Point := {point1, point2, point3}; point4 ∉ h
  non_colliear_1: ¬ collinear_3 point1 point2 point3
  non_colliear_2: ¬ collinear_3 point2 point3 point4
  non_colliear_3: ¬ collinear_3 point3 point4 point1
  non_colliear_4: ¬ collinear_3 point4 point1 point2



example (q: Quadrilateral) : q.point1 ≠ q.point2 := by
  let h1 := q.ne_1
  simp at h1
  rw [not_or] at h1
  let h3 := h1.left
  rw [← @ne_eq] at h3
  exact h3







--example : ∃! a : ℝ, 3 * a + 1 = 7 := by
--  use 2
--  dsimp
--  constructor
--  · numbers
--  intro y hy
--  calc
--    y = (3 * y + 1 - 1) / 3 := by ring
--    _ = (7 - 1) / 3 := by rw [hy]
--    _ = 2 := by numbers
--def line_for_points (A B: Point) : Line :=


--def segment_line (AB : Segment) :=
--def parallel_segments () :=

variable (q: Quadrilateral)

@[simp] def Quadrilateral.side1 (q: Quadrilateral) := Segment.mk q.point1 q.point2 (by
  let h1 := q.ne_1
  simp at h1
  rw [not_or] at h1
  let h3 := h1.left
  rw [<- @ne_eq] at h3
  exact h3
)

@[simp] def Quadrilateral.side2 (q: Quadrilateral) := Segment.mk q.point2 q.point3 (by
  let h1 := q.ne_2
  simp at h1
  rw [not_or, not_or] at h1
  let h3 := h1.right.left
  rw [<- @ne_eq] at h3
  exact h3
)

@[simp] def Quadrilateral.side3 (q: Quadrilateral) := Segment.mk q.point3 q.point4 (by
  let h1 := q.ne_3
  simp at h1
  rw [not_or, not_or] at h1
  let h3 := h1.right.right
  rw [<- @ne_eq] at h3
  exact h3
)

@[simp] def Quadrilateral.side4 (q: Quadrilateral) := Segment.mk q.point4 q.point1 (by
  let h1 := q.ne_4
  simp at h1
  rw [not_or, not_or] at h1
  let h3 := h1.left
  rw [<- @ne_eq] at h3
  exact h3
)


--def SimpleQuadrilateral := ¬ q.side1.intersects q.side3 ∧ ¬ q.side2.intersects q.side4

structure ConvexQuadrilateral where
  q: Quadrilateral
  non_intersecting: ¬ q.side1.intersects q.side3 ∧ ¬ q.side2.intersects q.side4

variable (cq: ConvexQuadrilateral)

@[simp] def ConvexQuadrilateral.angle1 : Angle :=
  Angle.from_3_points cq.q.point2 cq.q.point1 cq.q.point4 sorry sorry

@[simp] def ConvexQuadrilateral.angle2 : Angle :=
  Angle.from_3_points cq.q.point3 cq.q.point2 cq.q.point1 sorry sorry

@[simp] def ConvexQuadrilateral.angle3 : Angle :=
  Angle.from_3_points cq.q.point4 cq.q.point3 cq.q.point2 sorry sorry

@[simp] def ConvexQuadrilateral.angle4 : Angle :=
  Angle.from_3_points cq.q.point1 cq.q.point4 cq.q.point3 sorry sorry

@[simp] def Quadrilateral.diagonal13 : Segment := Segment.mk q.point1 q.point3 sorry
@[simp] def Quadrilateral.diagonal24 : Segment := Segment.mk q.point2 q.point4 sorry

@[simp] def ConvexQuadrilateral.diagonal_center (O: Point) := O ∈ cq.q.diagonal13.points ∧ O ∈ cq.q.diagonal24.points
@[simp] theorem ConvexQuadrilateral.exists_diagonal_center : ∃! O: Point, cq.diagonal_center O := by sorry

@[simp] def ConvexQuadrilateral.angle_sum := cq.angle1.value + cq.angle2.value + cq.angle3.value + cq.angle4.value
@[simp] theorem ConvexQuadrilateral.angle_sum_eq_360 :  cq.angle1.value + cq.angle2.value + cq.angle3.value + cq.angle4.value = 360 := sorry


@[simp] def ConvexQuadrilateral.triangle123 : Triangle where
  point1 := cq.q.point1
  point2 := cq.q.point2
  point3 := cq.q.point3
  point1_not_point2 := sorry
  point2_not_point3 := sorry
  point1_not_point3 := sorry
  not_on_same_line := sorry

@[simp] def ConvexQuadrilateral.triangle234 : Triangle where
  point1 := cq.q.point2
  point2 := cq.q.point3
  point3 := cq.q.point4
  point1_not_point2 := sorry
  point2_not_point3 := sorry
  point1_not_point3 := sorry
  not_on_same_line := sorry

@[simp] def ConvexQuadrilateral.triangle143 : Triangle where
  point1 := cq.q.point1
  point2 := cq.q.point4
  point3 := cq.q.point3
  point1_not_point2 := sorry
  point2_not_point3 := sorry
  point1_not_point3 := sorry
  not_on_same_line := sorry

@[simp] def ConvexQuadrilateral.triangle142 : Triangle where
  point1 := cq.q.point1
  point2 := cq.q.point4
  point3 := cq.q.point2
  point1_not_point2 := sorry
  point2_not_point3 := sorry
  point1_not_point3 := sorry
  not_on_same_line := sorry




--theorem SimpleQuadrilateral.angle_sum


  --let leftR := Ray.mk

@[simp] def Parallelogram := parallel_segments cq.q.side1 cq.q.side3 ∧ parallel_segments cq.q.side2 cq.q.side4

@[simp] theorem Parallelogram.angle1_con_angle3 (h: Parallelogram cq): cq.angle1 ≅ cq.angle3 := sorry
@[simp] theorem Parallelogram.angle2_con_angle4 (h: Parallelogram cq) : cq.angle2 ≅ cq.angle4 := sorry

@[simp] theorem Parallelogram.side1_con_side3 (h: Parallelogram cq): cq.q.side1 ≅ cq.q.side3 := sorry
@[simp] theorem Parallelogram.side2_con_side4 (h: Parallelogram cq) : cq.q.side2 ≅ cq.q.side4 := sorry

theorem Parallelogram.equal_opposite_sides (h: Parallelogram cq) : (cq.q.side1 ≅ cq.q.side3) ∧ (cq.q.side2 ≅ cq.q.side4) := sorry

@[simp] def Rectangle := Parallelogram cq ∧ cq.angle1.value = 90 ∧ cq.angle2.value = 90 ∧ cq.angle3.value = 90 ∧ cq.angle4.value = 90
def Square := Parallelogram cq ∧ cq.angle1.value = 90 ∧ cq.angle2.value = 90 ∧ cq.angle3.value = 90 ∧ cq.angle4.value = 90

@[simp] def Quadrilateral.perimeter := q.side1.length + q.side2.length + q.side3.length + q.side4.length
