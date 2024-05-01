import Mathlib.Tactic
import Geometry.Basic

-- congruence of segments

@[simp] def Segment.congr (AB BC: Segment) := AB.length = BC.length
@[simp] def Angle.congr (A B: Angle) := A.value = B.value



notation:40 AB " ≅ " BC:66 => Segment.congr AB BC
notation:40 A " ≅ " B:66 => Angle.congr A B


example (AB BC: Segment): Segment.congr AB BC ↔ AB ≅ BC := by
  simp

instance : Equivalence Segment.congr where
  refl := by sorry
  symm := by sorry
  trans := by sorry


--theorem segment_construction (AB : Segment) (CD: Ray) :
--  ∃! (E: Point) (CE: Segment), CE.point1 = CD.start ∧ E = CE.point2 ∧ CE ≅ AB := by sorry

def Segment.from_points (AB: Segment) (A B: Point) := AB.point1 = A ∧ AB.point2 = B

theorem segment_addition (A B C A' B' C': Point) (AB A'B' BC B'C' AC A'C' : Segment)
  (h: A - B - C) (h2: A' - B' - C') (h3: AB ≅ A'B') (h4: BC ≅ B'C')
  (h5: AB.from_points A B ∧ A'B'.from_points A' B' ∧ BC.from_points B C ∧ B'C'.from_points B' C' ∧ A'C'.from_points A' C')
  : AC ≅ A'C'
  := sorry

theorem segment_subtraction (A B C A' B' C': Point) (AB A'B' BC B'C' AC A'C' : Segment)
  (h: A - B - C) (h2: A' - B' - C') (h3: AB ≅ A'B') (h4: AC ≅ A'C')
  (h5: AB.from_points A B ∧ A'B'.from_points A' B' ∧ BC.from_points B C ∧ B'C'.from_points B' C' ∧ A'C'.from_points A' C')
  : BC ≅ B'C'
  := sorry

theorem one_midpoint (AB: Segment) : ∃! C: Point, C ∈ AB.points ∧ distance AB.point1 C = distance C AB.point2 := by
  obtain ⟨AB_l, h, k⟩  := segment_unique_line AB
  let A := AB.point1
  let B := AB.point2
  let A_val := value_on_line A AB_l h.left
  let B_val := value_on_line A AB_l h.left
  sorry



instance Angle.congr_eq : Equivalence Angle.congr where
  refl := by
    intro j
    rfl
  symm := by
    unfold Angle.congr
    exact fun {x y} a ↦ id a.symm
  trans := by
    unfold Angle.congr
    intro x y z l m
    rw [l, m]
