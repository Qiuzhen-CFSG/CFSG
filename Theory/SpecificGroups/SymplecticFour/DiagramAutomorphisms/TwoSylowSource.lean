module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel

/-!
# Diagram-moving two-subgroups and the marked outer involution

For the actual matrix group Sp₄(F), |F| = 2^m with m > 1, the exceptional
graph automorphism generates the cyclic outer group of order 2m. A two-subgroup
of automorphisms containing a diagram-moving element therefore maps onto the
full Sylow two-subgroup of the outer group. Its order is the two-part of 2m,
which is at least four when m is even.

In even degree the unique outer involution is the class of the coefficient
Frobenius raised to m/2. Every lift has the corresponding explicit inner-field
form, without an assumption that the lift itself is an involution. Such a lift
preserves the diagram. If it preserves either actual local residual, its
induced SL₂ action is non-inner: companion-matrix traces detect the field map,
including the full scalar contribution in the plane-parabolic quotient.

These results use the proved semilinear classification and the literal quotient
by the inner automorphisms. The final local-action theorems apply them to the
actual point and plane residuals and their proved two-core quotient maps.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, Lemmas 2.4.23(5) and 2.4.24(2);
GLS3, Theorem 2.5.12(e), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Subgroup ExceptionalGraph InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Field F] [Finite F] [CharP F 2] in
private theorem field_card_gt_two {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m) :
    2 < Nat.card F := by
  rw [hcard]
  exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hm

private theorem diagram_permutation_card_le (hF : 2 < Nat.card F) :
    Nat.card (Equiv.Perm (parabolicClasses hF)) ≤ 2 := by
  let := Fintype.ofFinite (parabolicClasses hF)
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc : Fintype.card (parabolicClasses hF) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hF
  exact (Nat.factorial_le hc).trans (by decide)

private theorem diagram_permutation_square (hF : 2 < Nat.card F)
    (a : Equiv.Perm (parabolicClasses hF)) : a^2 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  apply (orderOf_dvd_natCard a).trans
  have hc := diagram_permutation_card_le hF
  have hp := Nat.card_pos (α := Equiv.Perm (parabolicClasses hF))
  interval_cases h : Nat.card (Equiv.Perm (parabolicClasses hF)) <;> norm_num

/-- The actual outer automorphism group has order twice the field degree. -/
theorem card_outer_eq_two_mul {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m) :
    Nat.card (MulAut.Outer (Sp F)) = 2*m := by
  have hF := field_card_gt_two hcard hm
  let ρ := outerDiagramAction hF
  have hk : Nat.card ρ.ker = m := by
    rw [show ρ.ker = (outerFieldHom (F := F)).range from
      outerDiagramAction_ker hF SemilinearClassification.inner_field_of_preservesDiagram]
    exact (Nat.card_congr (Equiv.ofInjective _ outerFieldHom_injective)).symm.trans
      (card_fieldAut hcard)
  have ht : ρ (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) graphAut) ≠ 1 := by
    intro he
    exact graphAut_not_preservesDiagram
      ((mem_parabolicClassAction_ker_iff hF graphAut).mp he)
  have hr : Nat.card ρ.range = 2 := by
    have hu : Nat.card ρ.range ≤ 2 :=
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        (diagram_permutation_card_le hF)
    have hl : 1 < Nat.card ρ.range := by
      apply Finite.one_lt_card_iff_nontrivial.mpr
      exact ⟨⟨⟨ρ (QuotientGroup.mk' _ graphAut), ⟨_,rfl⟩⟩,
        1, fun h => ht (congrArg Subtype.val h)⟩⟩
    omega
  rw [card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hr, hk]

/-- Cyclicity here uses the proved semilinear classification of the actual group. -/
theorem outer_cyclic {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m) :
    IsCyclic (MulAut.Outer (Sp F)) :=
  outer_isCyclic_of_card hcard hm SemilinearClassification.inner_field_of_preservesDiagram

private theorem sylow_of_cyclic_moving_two_subgroup
    {G H : Type*} [Group G] [Finite G] [IsCyclic G] [Group H]
    (ρ : G →* H) (hsq : ∀ a, (ρ a)^2 = 1)
    (B : Subgroup G) (hB : IsPGroup 2 B) (hb : ∃ b ∈ B, ρ b ≠ 1) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = B := by
  obtain ⟨P,hP⟩ := hB.exists_le_sylow
  obtain ⟨b,hb,hmove⟩ := hb
  obtain ⟨t,ht⟩ := IsCyclic.exists_monoid_generator (α := P)
  obtain ⟨k,hk⟩ := ht ⟨b,hP hb⟩
  have hodd : Odd k := by
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨j,rfl⟩ := he
      apply False.elim
      apply hmove
      have hh := congrArg (fun p : P => ρ p) hk
      simp only [Subgroup.coe_pow,map_pow] at hh
      rw [← hh, ← two_mul, pow_mul, hsq, one_pow]
    · exact ho
  have horder : orderOf b = Nat.card P := by
    have hh : b = (t : G)^k := (congrArg Subtype.val hk).symm
    rw [hh, orderOf_pow, Subgroup.orderOf_coe,
      (P.isPGroup'.orderOf_coprime hodd.coprime_two_left t).gcd_eq_one, Nat.div_one]
    exact orderOf_eq_card_of_forall_mem_powers ht
  refine ⟨P, (eq_of_le_of_card_ge hP ?_).symm⟩
  calc
    Nat.card P = Nat.card (zpowers b) := by rw [Nat.card_zpowers,horder]
    _ ≤ Nat.card B := card_le_of_le (zpowers_le.mpr hb)

/-- A two-subgroup moving the diagram has the full Sylow-two outer image. -/
theorem outer_image_sylow {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hmove : ∃ a ∈ A, ¬ PreservesDiagram a) :
    ∃ P : Sylow 2 (MulAut.Outer (Sp F)),
      (P : Subgroup (MulAut.Outer (Sp F))) =
        A.map (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))) := by
  let : IsCyclic (MulAut.Outer (Sp F)) := outer_cyclic hcard hm
  have hF := field_card_gt_two hcard hm
  apply sylow_of_cyclic_moving_two_subgroup (outerDiagramAction hF)
    (fun a => diagram_permutation_square hF _) _ (hA.map _)
  obtain ⟨a,ha,hmov⟩ := hmove
  refine ⟨QuotientGroup.mk' _ a, mem_map_of_mem _ ha, ?_⟩
  intro he
  exact hmov ((mem_parabolicClassAction_ker_iff hF a).mp he)

/-- Every subgroup of the actual cyclic outer group is cyclic. -/
theorem outer_image_cyclic {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (A : Subgroup (MulAut (Sp F))) :
    IsCyclic (A.map (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)))) := by
  let : IsCyclic (MulAut.Outer (Sp F)) := outer_cyclic hcard hm
  infer_instance

/-- The outer image has the exact two-part of twice the field degree. -/
theorem outer_image_card {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hmove : ∃ a ∈ A, ¬ PreservesDiagram a) :
    Nat.card (A.map (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)))) =
      2 ^ ((2*m).factorization 2) := by
  obtain ⟨P,hP⟩ := outer_image_sylow hcard hm A hA hmove
  rw [← hP, P.card_eq_multiplicity, card_outer_eq_two_mul hcard hm]

/-- For even field degree the moving outer image has at least four elements. -/
theorem four_le_outer_image_card {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (heven : Even m) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hmove : ∃ a ∈ A, ¬ PreservesDiagram a) :
    4 ≤ Nat.card (A.map (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)))) := by
  rw [outer_image_card hcard hm A hA hmove]
  have hd : 2^2 ∣ 2*m := by
    obtain ⟨k,rfl⟩ := heven
    exact ⟨k,by ring⟩
  have he := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : 2*m ≠ 0)).mp hd
  exact (by norm_num : 4=2^2) ▸ Nat.pow_le_pow_right (by decide) he

private theorem cyclic_square_eq_one_or {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (s : G) (hs : s^2 = 1) (hne : s ≠ 1) (a : G) (ha : a^2 = 1) :
    a = 1 ∨ a = s := by
  classical
  let := Fintype.ofFinite G
  by_contra! h
  have hl : ({1,s,a} : Finset G) ⊆ Finset.univ.filter (fun x : G => x^2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [hs,ha]
  have hc := (Finset.card_le_card hl).trans (IsCyclic.card_pow_eq_one_le (by decide : 0<2))
  simp [Finset.card_insert_of_notMem, Ne.symm hne, Ne.symm h.1, Ne.symm h.2] at hc

/-- The unique outer involution is represented by the coefficient-field involution.
The lift itself need not have order two. -/
theorem outer_involution_inner_field {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (heven : Even m) (a : MulAut (Sp F))
    (ha : orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) a) = 2) :
    ∃ g : Sp F, a = MulAut.conj g * fieldAutomorphism (frobeniusEquiv F 2 ^ (m/2)) := by
  let π : MulAut (Sp F) →* MulAut.Outer (Sp F) := QuotientGroup.mk' _
  change orderOf (π a) = 2 at ha
  let : IsCyclic (MulAut.Outer (Sp F)) := outer_cyclic hcard hm
  have hp : (π a)^2 = 1 := by simpa only [ha] using pow_orderOf_eq_one (π a)
  have hs : (π (graphAut (F := F)^m))^2 = 1 := by
    rw [← map_pow, graph_pow_square hcard, map_one]
  have hne : π (graphAut (F := F)^m) ≠ 1 := by
    intro h
    exact graph_pow_not_inner hcard hm ((QuotientGroup.eq_one_iff _).mp h)
  have he : π a = π (graphAut (F := F)^m) := by
    rcases cyclic_square_eq_one_or _ hs hne _ hp with hh | hh
    · have ho : orderOf (π a) = 1 := by rw [hh,orderOf_one]
      omega
    · exact hh
  have hi : a / graphAut^m ∈ MulAut.innerSubgroup (Sp F) :=
    QuotientGroup.eq_iff_div_mem.mp he
  obtain ⟨g,hg⟩ := hi
  refine ⟨g, ?_⟩
  rw [← graph_pow_eq_field_of_even heven]
  exact (eq_div_iff_mul_eq'.mp hg).symm

/-- In even degree every lift of the outer involution preserves the diagram. -/
theorem outer_involution_preservesDiagram {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (heven : Even m) (a : MulAut (Sp F))
    (ha : orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) a) = 2) :
    PreservesDiagram a := by
  obtain ⟨g,rfl⟩ := outer_involution_inner_field hcard hm heven a ha
  have hF := field_card_gt_two hcard hm
  apply (mem_parabolicClassAction_ker_iff hF _).mp
  exact (parabolicClassAction hF).ker.mul_mem
    ((mem_parabolicClassAction_ker_iff hF _).mpr (inner_preservesDiagram g))
    ((mem_parabolicClassAction_ker_iff hF _).mpr (field_preservesDiagram _))

/-- The coefficient map occurring in the distinguished outer involution has order two. -/
theorem half_frobenius_order {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (heven : Even m) : orderOf (frobeniusEquiv F 2 ^ (m/2)) = 2 := by
  rw [← frobenius_order hcard]
  apply orderOf_pow_orderOf_div
  · rw [frobenius_order hcard]
    omega
  · rw [frobenius_order hcard]
    exact even_iff_two_dvd.mp heven

omit [Finite F] [CharP F 2] in
private theorem field_eq_one_of_semilinear_matrix_inner
    (σ : F ≃+* F) (C D : Matrix (Fin 2) (Fin 2) F) (hDC : D*C = 1)
    (c : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      C * (Matrix.SpecialLinearGroup.map σ.toRingHom A).val * D =
        (c*A*c⁻¹).val) : σ = 1 := by
  apply RingEquiv.ext
  intro t
  let A : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![t,-1;1,0], by simp [Matrix.det_fin_two]⟩
  have he := congrArg Matrix.trace (h A)
  have hc : (c⁻¹).val*c.val = 1 := congrArg Subtype.val (inv_mul_cancel c)
  change Matrix.trace (C * (Matrix.SpecialLinearGroup.map σ.toRingHom A).val * D) =
    Matrix.trace (c.val*A.val*(c⁻¹).val) at he
  rw [Matrix.trace_mul_cycle, hDC, Matrix.one_mul,
    Matrix.trace_mul_cycle, hc, Matrix.one_mul] at he
  change Matrix.trace (A.val.map σ) = Matrix.trace A.val at he
  simpa [A, Matrix.trace, Fin.sum_univ_two] using he

/-- A nontrivial field contribution remains outer on the actual point-local quotient. -/
theorem pointSL2Action_semilinear_not_inner {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (g : Sp F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hL : pointLocal.map ((MulAut.conj g)*fieldAutomorphism σ).toMonoidHom = pointLocal) :
    pointSL2Action hcard hm ((MulAut.conj g)*fieldAutomorphism σ) hL ∉
      MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rintro ⟨c,hc⟩
  let d := pointParabolicQuotient ⟨g, point_semilinear_mem_parabolic hcard hm g σ hL⟩
  apply hσ
  apply field_eq_one_of_semilinear_matrix_inner σ d.val (d⁻¹).val
    (congrArg Subtype.val (inv_mul_cancel d)) c
  intro A
  have he := congrArg (fun b : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => (b A).val) hc
  rw [pointSL2Action_semilinear] at he
  exact he.symm

/-- A nontrivial field contribution remains outer on the actual plane-local quotient. -/
theorem planeSL2Action_semilinear_not_inner {m : ℕ} (hcard : Nat.card F = 2^m) (hm : 1 < m)
    (g : Sp F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hL : planeLocal.map ((MulAut.conj g)*fieldAutomorphism σ).toMonoidHom = planeLocal) :
    planeSL2Action hcard hm ((MulAut.conj g)*fieldAutomorphism σ) hL ∉
      MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rintro ⟨c,hc⟩
  let gp : planeParabolic (F := F) :=
    ⟨g, plane_semilinear_mem_parabolic hcard hm g σ hL⟩
  apply hσ
  apply field_eq_one_of_semilinear_matrix_inner σ (Plane.upperLeft gp) (Plane.upperLeft gp⁻¹)
    (by rw [← map_mul, inv_mul_cancel, map_one]) c
  intro A
  have he := congrArg (fun b : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => (b A).val) hc
  rw [planeSL2Action_semilinear] at he
  exact he.symm

/-- The distinguished outer involution acts non-inner on each preserved point-local SL₂ quotient. -/
theorem outer_involution_pointSL2Action_not_inner {m : ℕ}
    (hcard : Nat.card F = 2^m) (hm : 1 < m) (heven : Even m)
    (a : MulAut (Sp F))
    (ha : orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) a) = 2)
    (hL : pointLocal.map a.toMonoidHom = pointLocal) :
    pointSL2Action hcard hm a hL ∉ MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨g,rfl⟩ := outer_involution_inner_field hcard hm heven a ha
  apply pointSL2Action_semilinear_not_inner hcard hm g _ _ hL
  intro h
  have ho := half_frobenius_order hcard hm heven
  rw [h,orderOf_one] at ho
  contradiction

/-- The distinguished outer involution acts non-inner on each preserved plane-local SL₂ quotient. -/
theorem outer_involution_planeSL2Action_not_inner {m : ℕ}
    (hcard : Nat.card F = 2^m) (hm : 1 < m) (heven : Even m)
    (a : MulAut (Sp F))
    (ha : orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) a) = 2)
    (hL : planeLocal.map a.toMonoidHom = planeLocal) :
    planeSL2Action hcard hm a hL ∉ MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨g,rfl⟩ := outer_involution_inner_field hcard hm heven a ha
  apply planeSL2Action_semilinear_not_inner hcard hm g _ _ hL
  intro h
  have ho := half_frobenius_order hcard hm heven
  rw [h,orderOf_one] at ho
  contradiction

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
