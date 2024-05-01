import Mathlib.Tactic
import Geometry.Basic
import Geometry.Congruence

noncomputable section

@[ext]
structure Triangle where
  point1: Point
  point2: Point
  point3: Point
  point1_not_point2: point1 ≠ point2
  point2_not_point3: point2 ≠ point3
  point1_not_point3: point1 ≠ point3
  not_on_same_line: ¬ collinear_3 point1 point2 point3

@[simp] def Triangle.side1 (t: Triangle) := Segment.mk t.point1 t.point2 t.point1_not_point2
@[simp] def Triangle.side2 (t: Triangle) := Segment.mk t.point2 t.point3 t.point2_not_point3
@[simp] def Triangle.side3 (t: Triangle) := Segment.mk t.point3 t.point1 t.point1_not_point3.symm



@[simp] def Triangle.perimeter (t: Triangle)
  := t.side1.length + t.side2.length + t.side3.length

@[simp] def Triangle.angle1 (t: Triangle) : Angle :=
  Angle.from_3_points t.point2 t.point1 t.point3 (⟨t.point1_not_point2, ⟨t.point2_not_point3, t.point1_not_point3⟩⟩) t.not_on_same_line

@[simp] def Triangle.angle2 (t: Triangle) : Angle :=
  Angle.from_3_points t.point1 t.point2 t.point3 (⟨Ne.symm t.point1_not_point2, ⟨t.point1_not_point3, t.point2_not_point3⟩⟩)
    (by
      unfold collinear_3
      let k := t.not_on_same_line
      unfold collinear_3 at k
      push_neg
      push_neg at k
      intro AB
      intro p1 p2 p3
      exact k AB p2 p1 p3)

@[simp] def Triangle.angle3 (t: Triangle) : Angle :=
  Angle.from_3_points t.point2 t.point3 t.point1 (⟨Ne.symm t.point2_not_point3, ⟨Ne.symm t.point1_not_point2, Ne.symm t.point1_not_point3⟩⟩)
    (by
      unfold collinear_3
      let k := t.not_on_same_line
      unfold collinear_3 at k
      push_neg
      push_neg at k
      intro AB
      intro p1 p2 p3
      exact k AB p3 p2 p1)


theorem triangle_ord (ABC DEF: Triangle) (h: ABC = DEF)
  : let tr_verticies : Set Point := {DEF.point1, DEF.point2, DEF.point3};
    ABC.point1 ∈ tr_verticies ∧ ABC.point2 ∈ tr_verticies ∧ ABC.point3 ∈ tr_verticies
    := sorry

--theorem thriangle_eq (ABC DEF: Triangle) (h: ABC = DEF) :
--  (ABC.point1 = DEF.point1 ∧ ABC.point2 = DEF.point2 ∧ ABC.point3 = DEF.point3)
--  ∨ (ABC.point1 = DEF.point2 ∧ ABC.point2 = DEF.point3 ∧ ABC.point3 = DEF.point1)
--  ∨ (ABC.point1 = DEF.point3 ∧ ABC.point2 = DEF.point1 ∧ ABC.point3 = DEF.point2)
--  ∨ (ABC.point1 = DEF.point3 ∧ ABC.point2 = DEF.point2 ∧ ABC.point3 = DEF.point1)
--  ∨ (ABC.point1 = DEF.point3 ∧ ABC.point2 = DEF.point2 ∧ ABC.point3 = DEF.point1)  := sorry

example (ABC: Triangle) (h: ABC.side1.length = 4) (h2: ABC.side2.length = 5) (h3: Triangle.perimeter ABC = 12)
  : ABC.side3.length = sorry := by
  unfold Triangle.perimeter Triangle.side1 Triangle.side2 Triangle.side3 Segment.length at h3
  simp at h3
  unfold Triangle.side1 at h
  unfold Segment.length at h
  unfold Triangle.side3
  unfold Segment.length
  sorry
  --linarith! [h, h2, h3]

example (ABC: Triangle) (h: ABC.side1.length = 4) (h2: ABC.side2.length = 5) (h3: Triangle.perimeter ABC = 12)
  : ABC.side3.length = 3 := by
  unfold Triangle.perimeter Triangle.side1 Triangle.side2 Triangle.side3 Segment.length at h3
  simp at h3
  unfold Triangle.side1 at h
  unfold Segment.length at h
  unfold Triangle.side3
  unfold Segment.length
  linarith! [h, h2, h3]

@[simp] theorem Triangle.angle_sum {t: Triangle} : t.angle1.value + t.angle2.value + t.angle3.value = 180 := sorry

variable (t: Triangle)

def isosceles_triangle (t: Triangle) := t.side2 ≅ t.side3
--structure IsoscelesTriangle (t: Triangle) where
--  eq_sides := t.side1 = t.side2

variable (ist: isosceles_triangle t)


theorem IsoscelesTriangle.angle_eq : isosceles_triangle t ↔ (t.angle1 ≅ t.angle2) := sorry

def Trinangle.opposite (a: Angle) (s: Segment) :=
  (s.point1 ∈ a.left.ext_points ∧ s.point2 ∈ a.right.ext_points) ∨ (s.point2 ∈ a.left.ext_points ∧ s.point1 ∈ a.right.ext_points)

@[simp] def Triangle.flip (t: Triangle) : Triangle where
  point1 := t.point1
  point2 := t.point3
  point3 := t.point2
  point1_not_point2 := t.point1_not_point3
  point2_not_point3 := Ne.symm t.point2_not_point3
  point1_not_point3 := t.point1_not_point2
  not_on_same_line := sorry

@[simp] def Triangle.rotate (t: Triangle) : Triangle where
  point1 := t.point3
  point2 := t.point1
  point3 := t.point3
  point1_not_point2 := sorry
  point2_not_point3 := sorry
  point1_not_point3 := sorry
  not_on_same_line := sorry

@[simp] def Triangle.rotate_anti (t: Triangle) : Triangle := t.rotate.rotate

@[simp] theorem Triangle.altitude_exists1 : ∃! s: Segment, s.point1 = t.point1 ∧ s.perpendicular t.side2 := sorry
@[simp] theorem Triangle.altitude_exists2 : ∃! s: Segment, s.point1 = t.point2 ∧ s.perpendicular t.side3 := sorry
@[simp] theorem Triangle.altitude_exists3 : ∃! s: Segment, s.point1 = t.point3 ∧ s.perpendicular t.side1 := sorry

@[simp] def Triangle.altitude1 := t.altitude_exists1.choose
@[simp] def Triangle.altitude2 := t.altitude_exists2.choose
@[simp] def Triangle.altitude3 := t.altitude_exists3.choose


def RightTriangle (t: Triangle) := t.angle1.value = 90

def Triangle.similar (t1 t2: Triangle) :=
  t1.side1.length / t2.side1.length = t1.side2.length / t2.side2.length ∧
  t1.side2.length / t2.side2.length = t1.side3.length / t2.side3.length ∧
  t1.side1.length / t2.side1.length = t1.side3.length / t2.side3.length ∧
  t1.angle1.congr t2.angle1 ∧ t1.angle2.congr t2.angle2 ∧ t1.angle3.congr t2.angle3


theorem Triangle.similar_by_2sides (t1 t2: Triangle) (h: t1.side1.length / t2.side1.length = t1.side2.length / t2.side2.length)
  (h2: t1.angle1.congr t2.angle1) : t1.similar t2 := by sorry

theorem Triangle.similar_by_angle1_angle2 (t1 t2: Triangle) (h: t1.angle1.value = t2.angle1.value)
  (h2: t1.angle2.value = t2.angle2.value) : t1.similar t2 := by sorry

theorem Triangle.similar_by_angle1_angle3 (t1 t2: Triangle) (h: t1.angle1.value = t2.angle1.value)
  (h2: t1.angle3.value = t2.angle3.value) : t1.similar t2 := by sorry

theorem Triangle.similar_by_angle2_angle3 (t1 t2: Triangle) (h: t1.angle2.value = t2.angle2.value)
  (h2: t1.angle3.value = t2.angle3.value) : t1.similar t2 := by sorry

theorem Triangle.similar_by_3sides (t1 t2: Triangle) (h: t1.side1.length / t2.side1.length = t1.side2.length / t2.side2.length)
  (h2: t1.side1.length / t2.side1.length = t1.side3.length / t2.side3.length) : t1.similar t2 := by sorry


theorem RightTriangle.altitude1_on_side (t: Triangle) (right: RightTriangle t)
  : t.point2 - t.altitude1.point2 - t.point3 := sorry

theorem Triangle.side1_gr_zero (t: Triangle) : t.side1.length > 0 := by sorry
theorem Triangle.side2_gr_zero (t: Triangle) : t.side2.length > 0 := by sorry
theorem Triangle.side3_gr_zero (t: Triangle) : t.side3.length > 0 := by sorry

theorem Triangle.side1_ne_zero (t: Triangle) : t.side1.length ≠ 0 := by
  refine ne_of_gt ?h
  apply side1_gr_zero t

theorem Triangle.side2_ne_zero (t: Triangle) : t.side2.length ≠ 0 := by
  refine ne_of_gt ?h
  apply side2_gr_zero t

theorem Triangle.side3_ne_zero (t: Triangle) : t.side3.length ≠ 0 := by
  refine ne_of_gt ?h
  apply side3_gr_zero t



theorem Triangle.similarity_sides_div (t1 t2: Triangle) (h: t1.similar t2)
  : t1.side1.length / t1.side2.length = t2.side1.length / t2.side2.length
    ∧  t1.side2.length / t1.side3.length = t2.side2.length / t2.side3.length
    ∧  t1.side1.length / t1.side3.length = t2.side1.length / t2.side3.length
     := by
  unfold Triangle.similar at h
  obtain ⟨b1, b2, b3, _⟩ := h
  refine ⟨?h, ?h2, ?h3⟩
  exact (div_eq_div_iff_div_eq_div' t2.side1_ne_zero t1.side2_ne_zero).mp b1
  refine (div_eq_div_iff_div_eq_div' t2.side2_ne_zero t1.side3_ne_zero).mp b2
  refine (div_eq_div_iff_div_eq_div' ?_ ?_).mp b3
  exact side1_ne_zero t2
  exact side3_ne_zero t1
