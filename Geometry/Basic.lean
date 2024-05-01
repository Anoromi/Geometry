import Mathlib.Tactic

noncomputable section
axiom Point: Type
axiom Line: Type
axiom Plane: Type


axiom p_on_l (p : Point) (line: Line) : Prop
axiom p_on_pl (p : Point) (plane: Plane) : Prop
axiom l_on_pl (l : Line) (plane: Plane) : Prop

notation:40 A " ∈ " B:66 => p_on_l A B
notation:40 A " ∈ " B:66 => p_on_pl A B
notation:40 A " ⊂ " B:66 => l_on_pl A B

def line_points (l: Line) := {p : Point | p_on_l p l}
def different_3_poins (A B C: Point) := A ≠ B ∧ B ≠ C ∧ A ≠ C

-- 1
axiom only_one_line (A B: Point) (h: A ≠ B) : ∃! l: Line, A ∈ l ∧ B ∈ l


theorem line_equality (A B: Point) (AB AB': Line) (h: A ≠ B) (h2: A ∈ AB ∧ B ∈ AB) (h3: A ∈ AB' ∧ B ∈ AB') : AB = AB' := by
  let o := (only_one_line A B h).unique h2 h3
  exact o

def line_from_points (A B: Point) (h: A ≠ B) := (only_one_line A B h).choose


--axiom lies_on_line_eq (A B: Point) (l1 l2: Line) (h: A ≠ B) (h2: p_on_l A l1 ∧ p_on_l B l1) (h3: p_on_l A l2 ∧ p_on_l B l2) : A = B

def on_same_line (A B C: Point) := ∃ l: Line, p_on_l A l ∧ p_on_l B l ∧ p_on_l C l

-- 2
axiom only_one_plane (A B C: Point) (h: A ≠ B ∧ B ≠ C ∧ A ≠ C) (h2: ¬ on_same_line A B C) : ∃! pl: Plane, p_on_pl A pl ∧ p_on_pl B pl ∧ p_on_pl C pl

-- 3
axiom point_lies_line_lies (A B: Point) (l: Line) (pl: Plane) (A_B_neq: A ≠ B) (h: p_on_l A l ∧ p_on_l B l) (h2: p_on_pl A pl ∧ p_on_pl B pl) : l_on_pl l pl




def l_intersects_l (l1 l2: Line) := ∃ p: Point, p ∈ l1 ∧ p ∈ l2

def pl_intersects_pl (pl1 pl2: Plane) := ∃ l: Line, l_on_pl l pl1 ∧ l_on_pl l pl2

axiom at_least_2_points (l: Line): ∃ A B : Point, A ≠ B ∧ p_on_l A l ∧ p_on_l B l

theorem line_inequality (l1 l2: Line) : (∃ p: Point, (p_on_l p l1 ∧ ¬ p_on_l p l2) ∨ (¬ p_on_l p l1 ∧ p_on_l p l2)) ↔ l1 ≠ l2 := by
  apply Iff.intro
  . intro c1 c2
    rw [c2] at c1

    rw [← @not_forall_not] at c1
    rw [← iff_false] at c1
    have g1 : (∀ (x : Point), ¬(p_on_l x l2 ∧ ¬p_on_l x l2 ∨ ¬p_on_l x l2 ∧ p_on_l x l2)) := by
      intro x
      rw [and_not_self_iff, and_comm, and_not_self_iff]
      rw [or_false_iff]
      rw [not_false_eq_true]
      simp

    rw [c1] at g1
    exact g1

  . intro c2
    by_contra v
    push_neg at v

    apply Ne.elim c2
    obtain ⟨A, B, A_ne_B, A_on_l1, B_on_l1⟩  := (at_least_2_points l1)
    apply line_equality A B l1 l2 A_ne_B ⟨A_on_l1, B_on_l1⟩
    let k := (v A).left A_on_l1
    let k2 := (v B).left B_on_l1
    exact ⟨k, k2⟩

theorem only_one_intersection (l1 l2: Line) (l1_intersects_l2: l_intersects_l l1 l2) (l1_ne_l2: l1 ≠ l2)
    : ∃! p: Point, p ∈ l1 ∧ p ∈ l2 := by
  unfold l_intersects_l at l1_intersects_l2
  apply exists_unique_of_exists_of_unique

  . show ∃ x, x ∈ l1 ∧ x ∈ l2
    apply l1_intersects_l2

  . show ∀ (y₁ y₂ : Point), y₁ ∈ l1 ∧ y₁ ∈ l2 → y₂ ∈ l1 ∧ y₂ ∈ l2 → y₁ = y₂
    intro a b
    intro r1 r2
    obtain ⟨a_on_l1, a_on_l2⟩ := r1
    obtain ⟨b_on_l1, b_on_l2⟩ := r2
    by_contra v
    rw [← @ne_eq] at v
    let l1_eq_l2 := (only_one_line a b v).unique (And.intro a_on_l1 b_on_l1) (And.intro a_on_l2 b_on_l2)
    exact l1_ne_l2 l1_eq_l2


theorem t2 (AB: Line) (pl: Plane) (h: ¬ l_on_pl AB pl) : ∃! A: Point, p_on_l A AB ∧ p_on_pl A pl := sorry

theorem t3 (A: Point) (BC: Line) (h: ¬ p_on_l A BC) : ∃! ABC: Plane, p_on_pl A ABC ∧ l_on_pl BC ABC := sorry

theorem t4 (AB CD: Line) (h: AB ≠ CD) : ∃! ABC: Plane, l_on_pl AB ABC ∧ l_on_pl CD ABC := sorry

axiom distance (A B: Point) : ℝ
axiom distance_range (A B: Point) : distance A B ≥ 0
axiom distance_eq (A B: Point) : distance A B = 0 ↔ A = B
axiom distance_com (A B: Point): distance A B = distance B A

axiom value_on_line (A : Point) (AB: Line) (h: A ∈ AB) : ℝ
--axiom point_for_value (AB: Line) (v: ℝ) : ∃! P, P ∈ AB ∧ value_on_line P AB
--theorem value_equality (A B: Point) (AB: Line) (h : A ∈ AB ∧ B ∈ AB) : sorry := sorry
axiom distance_eqiv (A B : Point) (AB : Line) (h: A ∈ AB ∧ B ∈ AB): |value_on_line A AB h.left - value_on_line B AB h.right| = distance A B

def collinear_3 (A B C: Point) := ∃ AB: Line, p_on_l A AB ∧ p_on_l B AB ∧ p_on_l C AB
def collinear_on_line_3 (A B C: Point) (AB: Line) := (A ∈ AB) ∧ (B ∈ AB) ∧ (p_on_l C AB)

theorem collinear_3_flip_12 (A B C: Point) : collinear_3 A B C = collinear_3 B A C := by
  sorry

theorem collinear_3_flip_23 (A B C: Point) : collinear_3 A B C = collinear_3 A C B := by
  sorry

theorem collinear_3_flip_13 (A B C: Point) : collinear_3 A B C = collinear_3 C B A := by
  sorry

def between (A B C: Point) := collinear_3 A B C ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ distance A B + distance B C = distance A C

--infix:50 " * " => between

--notation:50 lhs:51 " * " mhs:51 " * " rhs:51  => between lhs mhs rhs
notation:40 A " - " B:66 " - " C:66 => between A B C
--notation:65 a " + " b:66 " + " c:66 => a + b - c

theorem between_ne_1_2 (A B C: Point) (h: A - B - C) : A ≠ B := h.right.left
theorem between_ne_2_3 (A B C: Point) (h: A - B - C) : B ≠ C := h.right.right.left
theorem between_ne_1_3 (A B C: Point) (h: A - B - C) : A ≠ C := h.right.right.right.left

theorem between_comm (A B C: Point) (he: A - B - C) : C - B - A := by
  unfold between at he
  unfold between
  unfold collinear_3
  unfold collinear_3 at he

  apply And.intro
  . use he.left.choose
    --refine ⟨?_, ?_, ?_ ⟩
    let c1 := he.left.choose_spec
    exact ⟨c1.right.right, c1.right.left, c1.left⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  . apply he.right.right.left.symm
  . apply he.right.left.symm
  . apply he.right.right.right.left.symm
  .
    rw [distance_com]
    rw [add_comm]
    nth_rewrite 1 [<- distance_com]
    rw [he.right.right.right.right]
    apply distance_com

def value_between (a b c: ℝ) := a + b = c ∧ a < b ∧ b < c

lemma l1 (A B C: Point) (l: Line) (h: collinear_on_line_3 A B C l) (h2: A ≠ B ∧ B ≠ C ∧ A ≠ C)
  (h3: value_between (value_on_line A l h.left) (value_on_line B l h.right.left)
        (value_on_line C l h.right.right))
  : A - B - C := by
    unfold between
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    unfold collinear_3
    unfold collinear_on_line_3 at h
    use l
    unfold collinear_on_line_3 at h
    exact h2.left
    exact h2.right.left
    exact h2.right.right
    unfold collinear_on_line_3 at h
    let dis := distance_eqiv A B l (⟨h.left, h.right.left⟩)

    rw [<- dis]

    sorry


theorem sqrt_sum_eq_sqr_sum (a b c: ℝ) (h: a ^ 2 + b ^ 2 = c ^ 2) (h2: c >= 0) : c = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [<- abs_eq_self.mpr h2]
  apply Eq.symm
  refine (Real.sqrt_eq_iff_sq_eq ?v ?l).mpr ?h4

  apply le_add_of_le_of_nonneg
  exact sq_nonneg a
  exact sq_nonneg b
  exact abs_nonneg c
  rw [sq_abs, h]


theorem one_between (A B C: Point) (h2: A ≠ B ∧ B ≠ C ∧ A ≠ C) :
  ((A - B - C) ∧ ¬ (B - A - C) ∧ ¬ (A - C - B)) ∨
  (¬ (A - B - C) ∧ (B - A - C) ∧ ¬ (A - C - B)) ∨
  (¬ (A - B - C) ∧ ¬ (B - A - C) ∧ (A - C - B))
   := by
  sorry

theorem one_between_A_B_C (A B C: Point) (h2: A - B - C) :
  ¬ (B - A - C) ∧ ¬ (A - C - B)
   := by
  sorry
-- b3
-- theorem


-- b4
theorem between_after (A B: Point) : ∃ C: Point, A - B - C := sorry
theorem betweenness_exist (A C: Point) : ∃ B D: Point, A - B - D ∧ A - B - D := sorry

--class Line (α : Type*) where
--  point1 : α -> Point
--  point2 : α -> Point
--  points: α -> Set Point
@[ext]
structure Segment where
  point1 : Point
  point2 : Point
  inequality: point1 ≠ point2
  --points: α -> Set Point


def inverseSegment (s: Segment) : Segment where
  point1 := s.point2
  point2 := s.point1
  inequality := Ne.symm s.inequality



def Segment.points (s: Segment) := { p: Point | s.point1 - p - s.point2 } ∪ {s.point1, s.point2}
def Segment.length (s: Segment) := distance s.point1 s.point2
def Segment.intersects (s1 s2: Segment) := ∃ v, v ∈ s1.points ∧ v ∈ s2.points

def Segment.split_by (AB AC CB: Segment) := AB.point1 = AC.point1 ∧ AC.point2 = CB.point1 ∧ AB.point2 = CB.point2 ∧ AC.point2 ∈ AB.points

theorem Segment.split_length (AB AC CB: Segment) (h2: AB.split_by AC CB) : AC.length + CB.length = AB.length := sorry

axiom segment_eq (s1 s2 : Segment) : s1 = s2 ↔ s1.points = s2.points


def parallel_lines (AB CD: Line) := ¬ ∃ p, p ∈ AB ∧ p ∈ CD


theorem segment_unique_line (AB: Segment) : ∃! l: Line, AB.point1 ∈ l ∧ AB.point2 ∈ l := sorry


def Segment.line (AB : Segment) : Line :=
  Classical.choose (segment_unique_line AB)

def Segment.line_spec (AB : Segment) :=
  (segment_unique_line AB).choose_spec


def Segment.inverse (AB : Segment) : Segment where
  point1 := AB.point2
  point2 := AB.point1
  inequality := Ne.symm AB.inequality


theorem Segment.inverse_length : ∀ AB: Segment, AB.length = AB.inverse.length := sorry

def parallel_segments (AB CD: Segment) := parallel_lines AB.line CD.line

theorem Segment.between_in_points (AB: Segment) (C: Point) (h: AB.point1 - C - AB.point2) : C ∈ AB.points := by sorry

@[ext]
structure Ray where
  start: Point
  l: Line
  ext_points: Set Point
  start_on_l: start ∈ l
  ext_points_on_line: ∀ p ∈ ext_points, p ∈ l
  start_never_between : ∀ p1 ∈ ext_points, ∀ p2 ∈ ext_points, p1 ≠ p2 -> ¬ p1 - start - p2
  ray_not_segment: ∀ p1 p2, p1 ∈ l -> p2 ∈ ext_points -> ((start - p2 - p1) ∨ (start - p1 - p2)) -> p1 ∈ ext_points
  --ray_not_segment := ∀ p1, p2
  --hehe := ∀ p : l_cont_p l, true
  --hehe := ∀ p : Point, p ∈ l →
  --all_points_on_line := ∀ p1 ∈ points, ¬ ∃ v, v ∈ l ∧ ¬ v ∈ points ∧
  --point1 : Point
  --point2 : Point
  --inequality: point1 ≠ point2

--def Ray.points (r: Ray) := { p: Point | r.point1 - p - r.point2 ∨ r.point1 - r.point2 - p } ∪ {r.point1, r.point2}


def Ray.points (r: Ray) := { r.start } ∪ r.ext_points

def Ray.opposite (AB AC: Ray) := AB.start = AC.start ∧ ∃ P ∈ AB.ext_points, ∃ P2 ∈ AC.ext_points, P - AB.start - P2
theorem Ray.exists_from_points (start ext: Point) (h: start ≠ ext) : ∃ r: Ray, r.start = start ∧ start ∈ r.l ∧ ext ∈ r.l ∧ ext ∈ r.ext_points := sorry

--def Ray.from_points (start ext: Point) (h: start ≠ ext) := (Ray.exists_from_points start ext h).choose
@[simp]
def Ray.from_points (start ext: Point) (h: start ≠ ext) : Ray :=
  let one_line := (only_one_line start ext h)
  let line := one_line.choose
  let ka := one_line.choose_spec.right line
  --let ⟨⟨bi, vi⟩⟩ := one_line
  --let he := Classical.choice <| let ⟨x, px⟩ := one_line;
  --let ke := one_line.exists.snd
  --let bi := Classical.choice <| let ⟨x, px⟩ := one_line; ⟨⟨x, px⟩⟩

  {
    start := start
    l := line
    ext_points := { p | p ∈ line ∧ ¬ p - start - ext}
    ext_points_on_line := by
      intro p
      dsimp
      intro v
      apply v.left

    start_on_l := by
      apply one_line.choose_spec.left.left
    start_never_between := by
      intro A c1 C c2 A_ne_C
      let k := c1.out
      let other_choose := (Classical.choose one_line)
      let ch := (Classical.choose_spec one_line).left
      unfold between
      push_neg
      intro col_A_start_C A_ne_start start_ne_C A_ne_C
      let k1 := c1.out.right
      let k2 := c2.out.right
      dsimp at c1
      dsimp at c2
      --rw [one_between_A_B_C] at k1
      rw [ne_eq]
      by_contra g
      let he := one_between_A_B_C A start C ⟨col_A_start_C, A_ne_start, start_ne_C, A_ne_C, g⟩
      let he2 := one_between_A_B_C A start C ⟨col_A_start_C, A_ne_start, start_ne_C, A_ne_C, g⟩



      sorry
    ray_not_segment := sorry
  }


def Ray.formed_by (r: Ray) (A B: Point) := r.start = A ∧ B ∈ r.ext_points

theorem Ray.exists_point_on_ext (r: Ray) : ∃ p, p ∈ r.ext_points := by sorry



--theorem ray_ext (C: Point) (AB: Ray) (h: C ∈ AB.ext_points ∧ C ≠ AB.start) :
--  --let AC := Ray.mk AB.point1 C (Ne.symm h.right);
--  let AC := Ray.from_points AB.start C (Ne.symm h.right)
--  AB = AC := sorry

--theorem ray_ext (C: Point) (AB: Ray) (h: C ∈ AB.ext_points ∧ C ≠ AB.start) :
--  --let AC := Ray.mk AB.point1 C (Ne.symm h.right);
--  let AC := Ray.from_points AB.start C (Ne.symm h.right)
--  C ∈ AC.l := by
--  let AC := Ray.from_points AB.start C (Ne.symm h.right)
--  rw [Ray.from_points]
--  let line := Ray.from_points.proof_3 AB.start C (Ne.symm h.right)
--  --rw [line]
--
--
--  --apply?
--  --refine
--  --  let AC := Ray.from_points AB.start C (Ne.symm h.right);
--
--  sorry

theorem Ray.point_on_both (AB AC: Ray) (h: AB.start = AC.start) (h2: ∃ B, B ∈ AB.ext_points ∧ B ∈ AC.ext_points) :
  AB = AC := by
  let B := h2.choose
  let B_properties := h2.choose_spec
  let B_on_AB := B_properties.left
  let B_on_AC := B_properties.right
  --rw [Ray.ext_points] at B_on_AB
  simp at B_on_AB
  by_contra AB_not_AC
  rw [← @ne_eq] at AB_not_AC

  sorry

theorem Ray.between_eq (AB AC: Ray) (h: AB.start = AC.start) (h2: ∃ B C, B ∈ AB.ext_points ∧ C ∈ AC.ext_points ∧ AB.start - B - C) :
  AB = AC := by sorry

theorem ray_line_eq (AB AC: Ray) (h: AB.start = AC.start) (h2: AB.ext_points = AC.ext_points) : AB = AC := by
  refine (Ray.ext AC AB (id h.symm) ?l (id h2.symm)).symm
  let B := AB.exists_point_on_ext.choose


  sorry

theorem ray_eq (AB AC: Ray) (D: Point) (h: AB.start = AC.start) (h2: D ∈ AB.ext_points) (h3: D ∈ AC.ext_points) : AB = AC := by
  refine Ray.ext AB AC h ?l ?ext_points
  sorry
  sorry


@[ext]
structure Angle where
  left: Ray
  right: Ray
  same_start: left.start = right.start
  not_same_line: left.l ≠ right.l

def Angle.center (ABC: Angle) := ABC.left.start

--theorem angle_eq (ABC: Angle) (B₁ C₁ : Point) (h: B₁ ∈ ABC.left.points ∧ B₁ ≠ ABC.center) (h2: C₁ ∈ ABC.right.points ∧ C₁ ≠ ABC.center) :
--  let AB₁C₁ := Angle.mk (Ray.from_points ABC.center B₁ (Ne.symm h.right)) (Ray.from_points ABC.center C₁ (Ne.symm h2.right)) sorry sorry;
--  ABC = AB₁C₁
--  := sorry

theorem segment_eq_point_eq (AB CD: Segment) (h: AB = CD) : (AB.point1 = CD.point1 ∧ AB.point2 = CD.point2) ∨ (AB.point1 = CD.point2 ∧ AB.point2 = CD.point1) := sorry

--@[simp] theorem Angle.fr (B A C: Point) (h: A ≠ B ∧ B ≠ C ∧ A ≠ C) (h2: ¬ collinear_3 A B C) :
--  ∃ BAC: Angle, BAC.center = A ∧ BAC.left.formed_by A C ∧ BAC.right.formed_by A B := by
--  let AB := Ray.from_points A B h.left
--  let AB_l := only_one_line A C h.right.right
--  let AC := Ray.from_points A C h.right.right
--  let AC_l := only_one_line A B h.left
--  --let ABh := Ray.exists_from_points A B h.left
--  --let ACh := Ray.exists_from_points A C h.right.right
--  --let AB := ABh.choose
--  --let AC := ACh.choose
--  --let ABs := ABh.choose_spec
--  --let ACs := ACh.choose_spec
--  let Bar : Angle := {
--    left := AC
--    right := AB
--    not_same_line := by
--      unfold collinear_3 at h2
--      push_neg at h2
--      let non_coll_AB := h2 AB.l
--      rw [<- line_inequality]
--      use C
--      apply Or.intro_left
--      apply And.intro
--      .
--        let l := only_one_line A C h.right.right
--        apply l.choose_spec.left.right
--      . refine non_coll_AB ?_ ?_
--
--        sorry
--  }
--  use Bar
--  unfold center
--
--  sorry

def Angle.from_3_points (B A C: Point) (h: A ≠ B ∧ B ≠ C ∧ A ≠ C) (h2: ¬ collinear_3 A B C) : Angle :=
  let AB := Ray.from_points A B h.left
  let AB_l := only_one_line A B h.left
  let AC := Ray.from_points A C h.right.right
  {
    left := AC
    right := AB
    not_same_line := by
      unfold collinear_3 at h2
      push_neg at h2
      let non_coll_AB := h2 AB.l
      rw [<- line_inequality]
      use C
      apply Or.intro_left
      apply And.intro
      .
        let l := only_one_line A C h.right.right
        apply l.choose_spec.left.right
      . refine non_coll_AB ?_ ?_
        apply AB_l.choose_spec.left.left
        apply AB_l.choose_spec.left.right
    same_start := by rfl
    --inequality := by
    --  apply Ne.symm
    --  intro v
    --  have gi : AB.l = AC.l := by
    --    exact congrArg Ray.l (Eq.symm v)
    --  have gne : AB.l ≠ AC.l := by
    --    apply Ne.symm
    --    rw [<- line_inequality]
    --    use C
    --    apply Or.intro_left
    --    apply And.intro
    --    . apply ACs.right.right.left
    --    .
    --      unfold collinear_3 at h2
    --      push_neg at h2
    --      let ji := h2 AB.l  ABs.right.left ABs.right.right.left
    --      apply ji
    --  exact gne gi
    --starteq := sorry
    --non_opposite := sorry
  }


@[simp] def Angle.flip (a: Angle) : Angle where
  left := a.right
  right := a.left
  same_start := a.same_start.symm
  not_same_line := Ne.symm a.not_same_line

axiom angle_measure (a: Angle) : ℝ
axiom angle_measure_bounds (a: Angle) : angle_measure a < 180 ∧ angle_measure a > 0

@[simp] def Angle.value (a: Angle) := angle_measure a

@[simp] axiom angle_flip_measure (a: Angle) : angle_measure a = angle_measure a.flip

@[simp] theorem Angle.flip_value (a: Angle) : a.value = a.flip.value := by apply angle_flip_measure


--example (A B C: Point) (h: A ≠ B ∧ B ≠ C ∧ A ≠ C) (h2: ¬ collinear_3 A B C) : C ∈ (Angle.from_3_points B A C h h2).left.l := by
--  let k := (Angle.from_3_points B A C h h2)
--  let AC := k.left
--  unfold Angle.from_3_points
--  let ABh := Angle.from_3_points.proof_1 B A C h;
--  let ACh := Angle.from_3_points.proof_2 B A C h;
--  let AB := Exists.choose ABh;
--  let AC := Exists.choose ACh;
--  let ABs := Angle.from_3_points.proof_3 B A C h;
--  let ACs := Angle.from_3_points.proof_4 B A C h;
--  simp
--
--  --refine
--  --  Ray.ext_points_on_line
--  --    (let ABh := Angle.from_3_points.proof_1 B A C h;
--  --      let ACh := Angle.from_3_points.proof_2 B A C h;
--  --      let AB := Exists.choose ABh;
--  --      let AC := Exists.choose ACh;
--  --      let ABs := Angle.from_3_points.proof_3 B A C h;
--  --      let ACs := Angle.from_3_points.proof_4 B A C h;
--  --      { left := AC, right := AB, not_same_line := Angle.from_3_points.proof_5 B A C h h2 } : Angle).left
--  --    C ?_
--
--  --rename Angle => he
--  --unfold Angle.from_3_points
--  --simp
--
--
--  --refine Ray.ext_points_on_line (Exists.choose (Angle.from_3_points.proof_2 B A C h)) C ?_
--
--
--  sorry


theorem parallel_angle_lines (BAC ACD: Angle) (h: BAC.right = ACD.right)
  (h2: parallel_lines BAC.left.l ACD.left.l) : BAC.value = ACD.value := sorry

def Segment.perpendicular (AB CD: Segment) :=
  let ⟨A, B⟩  := (AB.point1, AB.point2)
  let ⟨C, D⟩  := (CD.point1, CD.point2)

  B ∈ CD.line ∧
    (Xor' (B = D) (∃! ABD: Angle, ABD.left.formed_by B A ∧ ABD.right.formed_by B D ∧ ABD.value = 90)) ∧
    (Xor' (B = C) (∃! ABC: Angle, ABC.left.formed_by B A ∧ ABC.right.formed_by B C ∧ ABC.value = 90))

@[simp] def Angle.can_be_formed_by_segments (AB AC: Segment) := AB.point1 = AC.point1 ∧ AB.line ≠ AC.line
def Angle.form_angle_from_segment (AB AC: Segment) (h: Angle.can_be_formed_by_segments AB AC) : Angle :=
  Angle.from_3_points AB.point2 AB.point1 AC.point2 (
    by
      apply And.intro
      apply AB.inequality
      apply And.intro
      let lines := h.right
      unfold Segment.line at lines
      intro v
      have k : AB = AC := by
        apply (Segment.ext AC AB h.left.symm v.symm).symm
      have b : AB ≠ AC := by
        exact ne_of_apply_ne (fun S ↦ Classical.choose (segment_unique_line S)) lines
      exact b k
      rw [h.left]
      apply AC.inequality
  ) (by
    unfold collinear_3
    push_neg
    intro AB_l
    intro k m
    have b : AB_l = AB.line := by
      refine line_equality AB.point1 AB.point2 AB_l ?t AB.inequality ?t3 ?t4
      exact And.intro k m
      let aspects := (segment_unique_line AB).choose_spec
      exact aspects.left

    simp at h
    intro ji

    refine @Ne.elim Line AB.line AC.line ?_ ?_
    exact h.right
    apply line_equality AB.point1 AC.point2 AB.line
    . rw [h.left]
      apply AC.inequality
    . refine And.intro AB.line_spec.left.left ?_
      rw [<- b]
      exact ji
    . rw [h.left]
      apply AC.line_spec.left
  )


--theorem perpendicular_not_on_same_line (AB CD : Segment) (h: AB.perpendicular CD) :
--  ¬ (collinear_3 AB.point1 AB.point2 CD.point1) ∧ ¬ (collinear_3 AB.point1 AB.point2 CD.point2) := by sorry

--theorem Ray.ext_eq (A B C: Point) (h: Ray.ext_iff) : AB = AC := by
--  --apply Ray.ext
--
--  sorry
--  sorry
--  sorry

theorem Segment.perperndicular_not_on_same_line_point1 (AB CD: Segment) (h: AB.perpendicular CD) (h2: AB.point2 ≠ CD.point1) :
  ¬ (collinear_3 AB.point1 AB.point2 CD.point1) := by sorry

theorem Segment.perperndicular_not_on_same_line_point2 (AB CD: Segment) (h: AB.perpendicular CD) (h2: AB.point2 ≠ CD.point2) :
  ¬ (collinear_3 AB.point1 AB.point2 CD.point2) := by sorry
