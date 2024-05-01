import Geometry.Basic
import Geometry.Quadrilateral
import Geometry.Triangle
import Geometry.Congruence


example (ABCD: ConvexQuadrilateral) (h: Parallelogram ABCD)
  (per: ABCD.q.perimeter = 24) (h3: ABCD.angle2.value = 160)
  (h4: Angle.can_be_formed_by_segments ABCD.q.side4.inverse ABCD.q.diagonal13)
  (h5: (Angle.form_angle_from_segment ABCD.q.side4.inverse ABCD.q.diagonal13 h4).value = 10)
  : true = true := by

  let diagonal_angle := Angle.form_angle_from_segment ABCD.q.side4.inverse ABCD.q.diagonal13 h4
  let ACD_t := ABCD.triangle143.flip


  have ACD_eq_ABD : ACD_t.angle3 ≅ ABCD.angle2 := by
    apply Angle.congr_eq.trans
    . show ACD_t.angle3 ≅ ABCD.angle4.flip
      rfl
    . show ABCD.angle4.flip ≅ ABCD.angle2
      apply Angle.congr_eq.symm
      unfold Angle.congr
      nth_rewrite 1 [<- Angle.flip_value]
      apply (Parallelogram.angle2_con_angle4 ABCD h)



  have ACD_val : ACD_t.angle3.value = 160 := by
    rw [<- h3]
    unfold Angle.congr at ACD_eq_ABD
    apply ACD_eq_ABD


  have c2 : isosceles_triangle ACD_t := by
    apply (IsoscelesTriangle.angle_eq ACD_t).mpr
    let sum := ACD_t.angle_sum
    rw [ACD_val] at sum
    rw [Angle.flip_value] at sum
    have c1 : ACD_t.angle1.flip = diagonal_angle := by rfl
    rw [c1] at sum
    rw [h5] at sum

    have ADC_val : ACD_t.angle2.value = 10 := by linarith
    unfold Angle.congr

    rw [ADC_val]
    rw [Angle.flip_value]
    rw [c1]
    rw [h5]

  unfold Quadrilateral.perimeter at per
  have AD_eq_CD : ABCD.q.side4 ≅ ABCD.q.side3 := by
    unfold isosceles_triangle at c2
    simp [c2]
    simp at c2
    exact c2.symm

  have side4_length : ABCD.q.side4.length = 6 := by
    calc
      ABCD.q.side4.length = 4 * ABCD.q.side4.length / 4 := by linarith
      _ = (ABCD.q.side4.length + ABCD.q.side4.length + ABCD.q.side4.length + ABCD.q.side4.length) / 4 := by linarith
      _ = (ABCD.q.side4.length + ABCD.q.side4.length + ABCD.q.side3.length + ABCD.q.side4.length) / 4 := by
        nth_rewrite 3 [AD_eq_CD]
        simp
      _ = (ABCD.q.side4.length + ABCD.q.side2.length + ABCD.q.side3.length + ABCD.q.side4.length) / 4 := by
        nth_rewrite 2 [<- Parallelogram.side2_con_side4 ABCD h]
        simp
      _ = (ABCD.q.side1.length + ABCD.q.side2.length + ABCD.q.side3.length + ABCD.q.side4.length) / 4 := by
        nth_rewrite 1 [AD_eq_CD]
        nth_rewrite 1 [<- (Parallelogram.side1_con_side3 ABCD h)]
        simp
      _ = _ := by
        rw [per]
        linarith


  have side2_length : ABCD.q.side2.length = 6 := by
    calc
      ABCD.q.side2.length = ABCD.q.side4.length := by rw [Parallelogram.side2_con_side4 ABCD h]
      _ = 6 := side4_length

  have side1_length : ABCD.q.side1.length = 6 := by
    calc
      ABCD.q.side1.length = ABCD.q.side3.length := by rw [Parallelogram.side1_con_side3 ABCD h]
      _ = ABCD.q.side4.length := by rw [AD_eq_CD]
      _ = 6 := side4_length

  have side3_length : ABCD.q.side3.length = 6 := by
    linarith
  rfl


example (ABCD: ConvexQuadrilateral) (h: 2 * ABCD.angle1.value = ABCD.angle2.value
  ∧ 3 * ABCD.angle1.value = ABCD.angle3.value
  ∧ 2 * ABCD.angle1.value = ABCD.angle4.value) : sorry := by

  let a1 := ABCD.angle1.value
  let a2 := ABCD.angle2.value
  let a3 := ABCD.angle3.value
  let a4 := ABCD.angle4.value

  have c1 : ABCD.angle_sum = 8 * a1 := by
    calc
      ABCD.angle_sum = a1 + a2 + a3 + a4 := by rfl
      _ = a1 + a1 * 2 + a1 * 3 + a1 * 2 := by
        linarith
      _ = 8 * a1 := by linarith

  let t := ABCD.angle_sum_eq_360
  unfold ConvexQuadrilateral.angle_sum at c1
  rw [c1] at t

  have c2: a1 = 360 / 8 := by linarith

  have c3: a1 = 45 := by linarith
  have c4: a2 = 90 := by linarith
  have c5: a3 = 135 := by linarith
  have c6: a4 = 90 := by linarith

  sorry

example (A B C: ℝ) (h: A * C = B) : A = B / C := by
  refine EuclideanDomain.eq_div_of_mul_eq_right ?ha ?h
  sorry
  linarith

structure Eliminate {T V: Prop} where
  left(v: V): T
  right (t: T): V


theorem div_div_eq_mul_mul (A B C D: ℝ) (h: B ≠ 0) (h2: D ≠ 0) : A / B = C / D -> A * D = B * C := by
  intro h3
  refine (div_eq_iff_mul_eq h2).mp ?_
  apply Eq.symm
  calc
    A = A * B / B := by exact (eq_div_iff h).mpr rfl
    _ = (A / B) * B := by ring_nf
    _ = (C / D) * B := by rw [h3]
    _ = _ := by ring_nf

example (ABC: Triangle) (ABC_right: RightTriangle ABC) :
  ABC.side2.length ^ 2 = ABC.side1.length ^ 2 + ABC.side3.length ^ 2 := by
  let A := ABC.point1
  let B := ABC.point2
  let C := ABC.point3

  let AH := ABC.altitude1
  let H := AH.point2
  let AHc := ABC.altitude_exists1.choose_spec

  have A_eq_AH_point1 : A = AH.point1 := by
    let f := AHc.left.left
    apply f.symm

  let HBA : Triangle := {
    point1 := H,
    point2 := B,
    point3 := A,
    point1_not_point2 := by
      let l := RightTriangle.altitude1_on_side ABC ABC_right
      unfold between at l
      exact l.right.left.symm
    point2_not_point3 := by
      exact ABC.point1_not_point2.symm
    point1_not_point3 := by
      rw [A_eq_AH_point1]
      apply AH.inequality.symm

    not_on_same_line := by
      have c1 : ¬collinear_3 AH.point1 AH.point2 ABC.side2.point1 := by
        apply Segment.perperndicular_not_on_same_line_point1 AH ABC.side2 AHc.left.right
        let side := RightTriangle.altitude1_on_side ABC ABC_right
        rw [between] at side
        exact side.right.left.symm

      rw [collinear_3_flip_13, collinear_3_flip_23]
      have A_eq_AH_point1 : AH.point1 = A := by apply AHc.left.left
      rw [<- A_eq_AH_point1]
      apply c1
  }


  let HAC : Triangle := {
    point1 := H
    point2 := A
    point3 := C
    point1_not_point2 := by
      rw [A_eq_AH_point1]
      apply AH.inequality.symm
    point2_not_point3 := by
      apply ABC.point1_not_point3
    point1_not_point3 := by
      let l := RightTriangle.altitude1_on_side ABC ABC_right
      unfold between at l
      apply l.right.right.left
    not_on_same_line := by
      have c1 : ¬collinear_3 AH.point1 AH.point2 ABC.point3 := by
        apply Segment.perperndicular_not_on_same_line_point2 AH ABC.side2 AHc.left.right
        let side := RightTriangle.altitude1_on_side ABC ABC_right
        exact between_ne_2_3 ABC.point2 AH.point2 (Triangle.side2 ABC).point2 side

      rw [collinear_3_flip_12]
      have A_eq_AH_point1 : AH.point1 = A := by apply AHc.left.left
      rw [<- A_eq_AH_point1]
      apply c1
  }

  have HBA_right : RightTriangle HBA := by
    rw [RightTriangle]

    let b1 := ABC.altitude_exists1.choose_spec.left.right
    rw [Segment.perpendicular] at b1
    --dsimp at b1
    let ⟨v1, AH_forms_angle_with_C, AH_forms_angle_with_B⟩  := b1
    have H_ne_C : AH.point2 ≠ ABC.point3 := by
      let v :=  RightTriangle.altitude1_on_side ABC ABC_right
      apply between_ne_2_3
      apply v

    have AH_forms_angle_with_C :
      (∃! ABD,
      Ray.formed_by ABD.left AH.point2 AH.point1 ∧
        Ray.formed_by ABD.right AH.point2 (Triangle.side2 ABC).point2 ∧ Angle.value ABD = 90) ∧
        ¬AH.point2 = (Triangle.side2 ABC).point2 := by
      let g := AH_forms_angle_with_C.resolve_left
      apply g



      sorry

    have c1 : ∃! ABD, Ray.formed_by ABD.left AH.point2 AH.point1 ∧
      Ray.formed_by ABD.right AH.point2 ABC.point3 ∧ angle_measure ABD = 90 := by
      sorry
    sorry

  have HBA_sim_ABC : HBA.similar ABC := by
    apply Triangle.similar_by_angle1_angle2 HBA ABC
    unfold RightTriangle at HBA_right
    rw [HBA_right]
    rw [ABC_right]
    rw [Angle.flip_value]
    congr
    rw [Angle.flip]
    unfold Triangle.angle2
    apply Angle.ext
    .
      apply Ray.point_on_both
      rfl
      use AH.point2
      refine ⟨?b1, ?b2⟩
      sorry
      let b := ABC.angle2.left.ray_not_segment
      sorry

    . rfl

  have HAC_sim_ABC : HAC.similar ABC := by
    sorry

  let ⟨b1, b2, b3, b4, b5, b6⟩  := HBA_sim_ABC

  let ⟨g1, g2, g3, g4, g5, g6⟩  := HAC_sim_ABC



  have BH_HC_form_BC : ABC.side2.split_by HBA.side1.inverse HAC.side3.inverse := by
    rw [Segment.split_by]
    refine ⟨?_, ?_, ?_, ?_⟩
    rfl
    rfl
    rfl
    apply Segment.between_in_points
    let v := RightTriangle.altitude1_on_side ABC ABC_right
    rw [Triangle.altitude1] at v
    apply v

  let BC := ABC.side2
  let AB := ABC.side1
  let BA := HBA.side2
  let HB := HBA.side1

  let CA := ABC.side3
  let CH := HAC.side3

  have BC_len : ABC.side2.length = HB.length + CH.length := by
    rw [Segment.inverse_length HBA.side1]
    rw [Segment.inverse_length HAC.side3]
    apply Eq.symm
    apply Segment.split_length ABC.side2 HBA.side1.inverse HAC.side3.inverse BH_HC_form_BC


  have AB_eq_BA_l : AB.length = BA.length := by
    apply Segment.inverse_length


  have AB_eq_BC_HB : AB.length * AB.length = BC.length * HB.length := by
    have c1 : HB.length / AB.length = AB.length / BC.length := by
      let ⟨s1, _, _⟩  := Triangle.similarity_sides_div HBA ABC HBA_sim_ABC
      nth_rewrite 1 [Segment.inverse_length AB]
      apply s1
    rw [div_div_eq_mul_mul ]
    exact ABC.side2_ne_zero
    exact ABC.side1_ne_zero
    exact c1.symm

  have CA_eq_CH_BC : CA.length * CA.length = CH.length * BC.length :=  by
    have c1 : BC.length / CA.length = CA.length / CH.length := by
      let ⟨s1, s2, s3⟩  := Triangle.similarity_sides_div HAC ABC HAC_sim_ABC
      nth_rw 2 [Segment.inverse_length CA]
      apply s2.symm
    rw [div_div_eq_mul_mul]
    exact HAC.side3_ne_zero
    exact ABC.side3_ne_zero
    exact c1.symm

  have AB_CA_eq_BC : AB.length ^ 2 + CA.length ^ 2 = BC.length ^ 2 := by
    calc
      AB.length ^ 2 + CA.length ^ 2 = AB.length * AB.length + CA.length * CA.length := by linarith
      _ = BC.length * HB.length + CH.length * BC.length := by linarith
      _ = BC.length * (HB.length + CH.length) := by linarith
      _ = BC.length * BC.length := by rw [BC_len]
      _ = BC.length ^ 2 := by linarith

  exact AB_CA_eq_BC.symm



example (a b c d : ℝ)  (h: a / b = c / d) (h2: b ≠ 0) (h3: c ≠ 0)  : a / c = b / d := by
  exact (div_eq_div_iff_div_eq_div' h2 h3).mp h
--  exact (div_eq_div_iff h2 h3).mp h
--  sorry


--  --calc
--  --  A = B * C := h
--  apply?
--  norm_num
--  --rw [@division_def] at h
--  --rw? at h
--  --calc
--  --  A / B = A * A := by linarith
--  --  _ = B * C := by sorry
--
--  --have c1 : A ^ 2 = B * C := by
--  --  calc
--  --    A ^ 2 = A * A := by linarith
--  --    _ = B * C := by sorry
--
--  --sorry
--
--
----example (AB CD: Segment) (h: AB.length = 2 * CD.length) : sorry := sorry
----example (ABC: Triangle) (h: ABC.angle1.value = 2 * ABC.angle2.value) : sorry :=
----    ABC.angle1.value + ABC.angle1.value + ABC.angle1.value = 180
