module

public import Theory.SpecificGroups.PSL3Four.OuterPlane.FieldOccurrence
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# The linear and field cases of the inverted cubic in H.4.7

A highest-root transvection inverts an explicit binary cubic on its two
coordinates. Frobenius inverts a noncentral diagonal cubic. Conjugacy transports
these witnesses to all nonidentity involutions in the linear–field subgroup.
The proved standard-automorphism theorem reduces every remaining involution
to a linear–field–graph actor, retaining the actual projective quotient.

Source: Aschbacher–Smith H.4.7, printed pp.382–383 of refs/quasithin.pdf.
-/

public section
noncomputable section
open Matrix Subgroup
open Matrix.PSL3Four Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic

/-- Inversion of an element of order three transports through an actual
conjugacy of automorphisms. -/
theorem transport_inverted_cubic {G : Type*} [Group G] (a b d : MulAut G)
    (hd : MulAut.congr d a = b)
    (hb : ∃ y : G, orderOf y = 3 ∧ b y = y⁻¹) :
    ∃ y : G, orderOf y = 3 ∧ a y = y⁻¹ := by
  obtain ⟨y, hy, hby⟩ := hb
  refine ⟨d.symm y, (d.symm.orderOf_eq y).trans hy, ?_⟩
  apply d.injective
  rw [map_inv, d.apply_symm_apply]
  exact (MulEquiv.congr_fun hd y).trans hby

private def binaryCubicSL : SL :=
  ⟨!![0,0,1; 0,1,0; 1,0,1], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

private theorem binaryCubicSL_cube : binaryCubicSL ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,0,1;0,1,0;1,0,1] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  simp [pow_succ, Matrix.one_fin_three, CharTwo.add_self_eq_zero]

private theorem binaryCubic_ne_one : (binaryCubicSL : PSL) ≠ 1 := by
  intro h
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff binaryCubicSL).mp h)
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 2) hr
  exact zero_ne_one hh

private theorem binaryCubic_order : orderOf (binaryCubicSL : PSL) = 3 := by
  apply orderOf_eq_prime _ binaryCubic_ne_one
  exact (QuotientGroup.mk' (center SL)).map_pow binaryCubicSL 3 |>.symm.trans
    (congrArg (QuotientGroup.mk' (center SL)) binaryCubicSL_cube) |>.trans (map_one _)

/-- The literal highest-root transvection inverts a cubic in the actual PSL₃(4). -/
theorem root_inverts_cubic :
    ∃ y : PSL, orderOf y = 3 ∧
      MulAut.conj (Matrix.PSL3.EvenInnerCentralizers.root F) y = y⁻¹ := by
  refine ⟨binaryCubicSL, binaryCubic_order, ?_⟩
  have he : Matrix.PSL3.EvenInnerCentralizers.rootSL F * binaryCubicSL *
      (Matrix.PSL3.EvenInnerCentralizers.rootSL F)⁻¹ = binaryCubicSL⁻¹ := by
    apply mul_right_cancel (b := binaryCubicSL)
    rw [inv_mul_cancel]
    have hr : (Matrix.PSL3.EvenInnerCentralizers.rootSL F)⁻¹ =
        Matrix.PSL3.EvenInnerCentralizers.rootSL F :=
      inv_eq_of_mul_eq_one_left (by
        simpa only [pow_two] using Matrix.PSL3.EvenInnerCentralizers.rootSL_sq F)
    rw [hr]
    apply Subtype.ext
    change (!![1,0,1;0,1,0;0,0,1] : Matrix (Fin 3) (Fin 3) F) *
      !![0,0,1;0,1,0;1,0,1] * !![1,0,1;0,1,0;0,0,1] * !![0,0,1;0,1,0;1,0,1] = 1
    simp [Matrix.one_fin_three, CharTwo.add_self_eq_zero]
  exact congrArg (QuotientGroup.mk' (center SL)) he

private theorem binaryCubic_graph : graph F (binaryCubicSL : PSL) = (binaryCubicSL : PSL)⁻¹ := by
  have ht : Matrix.SpecialLinearGroup.transpose binaryCubicSL = binaryCubicSL := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [graph_mk, ht]
  rfl

/-- The marked graph involution inverts the symmetric binary cubic. -/
theorem graph_inverts_cubic : ∃ y : PSL, orderOf y = 3 ∧ graph F y = y⁻¹ :=
  ⟨binaryCubicSL, binaryCubic_order, binaryCubic_graph⟩

/-- The marked graph–field involution inverts that same binary cubic. -/
theorem graphField_inverts_cubic :
    ∃ y : PSL, orderOf y = 3 ∧ (pslFrobenius * graph F) y = y⁻¹ := by
  have hf : slFrobenius binaryCubicSL = binaryCubicSL := by
    apply Subtype.ext
    change (!![0,0,1;0,1,0;1,0,1] : Matrix (Fin 3) (Fin 3) F).map (fun x => x ^ 2) =
      !![0,0,1;0,1,0;1,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  refine ⟨binaryCubicSL, binaryCubic_order, ?_⟩
  rw [MulAut.mul_apply, binaryCubic_graph, map_inv, pslFrobenius_mk, hf]

/-- All nonidentity inner involutions invert a cubic. -/
theorem inner_inverts_cubic (a : MulAut PSL) (hi : a ∈ MulAut.innerSubgroup PSL)
    (hne : a ≠ 1) (hsq : a ^ 2 = 1) :
    ∃ y : PSL, orderOf y = 3 ∧ a y = y⁻¹ := by
  obtain ⟨x, rfl⟩ := hi
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  have hinj := MulAut.conj_injective_of_center_eq_bot
    (Group.IsPerfect.center_quotient_center_eq_bot SL)
  have hx : x ≠ 1 := fun hx => hne (hx ▸ map_one MulAut.conj)
  have hx2 : x ^ 2 = 1 := hinj (by rw [map_pow, hsq, map_one])
  obtain ⟨g, hg⟩ := Matrix.PSL3.EvenInnerCentralizers.exists_conjugator_root
    F (n := 2) (by decide) card_F x hx hx2
  apply transport_inverted_cubic _ _ (MulAut.conj g) _ root_inverts_cubic
  change MulAut.conj g * MulAut.conj x * (MulAut.conj g)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hg]

private def diagonalSL (u : Fˣ) : SL :=
  ⟨!![1,0,0; 0,(u : F),0; 0,0,(↑u⁻¹ : F)], by simp [Matrix.det_fin_three]⟩

private theorem unit_cube (u : Fˣ) : u ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := u)
  simpa only [Nat.card_units, card_F] using h

private theorem diagonalSL_cube (u : Fˣ) : diagonalSL u ^ 3 = 1 := by
  have hu : (u : F)^3 = 1 := congrArg Units.val (unit_cube u)
  have hi : (↑u⁻¹ : F)^3 = 1 := congrArg Units.val (unit_cube u⁻¹)
  apply Subtype.ext
  change (!![1,0,0;0,(u : F),0;0,0,(↑u⁻¹ : F)] : Matrix (Fin 3) (Fin 3) F)^3 = 1
  simpa [pow_succ, Matrix.one_fin_three, mul_assoc] using
    congrArg (fun p : F × F => (!![1,0,0;0,p.1,0;0,0,p.2] : Matrix (Fin 3) (Fin 3) F))
      (show ((u : F)^3, (↑u⁻¹ : F)^3) = (1,1) from Prod.ext hu hi)

private theorem diagonal_ne_one (u : Fˣ) (hu : u ≠ 1) : (diagonalSL u : PSL) ≠ 1 := by
  intro h
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff (diagonalSL u)).mp h)
  have h0 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 0) hr
  have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 1 1) hr
  exact hu (Units.ext (h1.symm.trans h0))

/-- Entrywise Frobenius inverts a noncentral diagonal element of order three. -/
theorem frobenius_inverts_cubic :
    ∃ y : PSL, orderOf y = 3 ∧ pslFrobenius y = y⁻¹ := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card Fˣ by rw [Nat.card_units, card_F])
  have hune : u ≠ 1 := by intro h; simp [h] at hu
  refine ⟨diagonalSL u, orderOf_eq_prime ?_ (diagonal_ne_one u hune), ?_⟩
  · exact (QuotientGroup.mk' (center SL)).map_pow (diagonalSL u) 3 |>.symm.trans
      (congrArg (QuotientGroup.mk' (center SL)) (diagonalSL_cube u)) |>.trans (map_one _)
  · have he : slFrobenius (diagonalSL u) = diagonalSL u ^ 2 := by
      apply Subtype.ext
      change (diagonalSL u).val.map (fun x => x ^ 2) = (diagonalSL u).val ^ 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonalSL, pow_two, Matrix.map_apply]
    have hi : diagonalSL u ^ 2 = (diagonalSL u)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa only [← pow_succ] using diagonalSL_cube u)
    rw [pslFrobenius_mk, he, hi]
    rfl

/-- A field automorphism of GF(4) is either trivial or squaring. -/
theorem coefficient_cases (σ : F ≃+* F) : σ = 1 ∨ σ = fieldFrobenius := by
  let τ : F →ₐ[ZMod 2] F :=
    (AlgEquiv.ofRingEquiv (f := σ) (fun z =>
      congrArg (fun f : ZMod 2 →+* F => f z)
        (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)))).toAlgHom
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) F).surjective τ
  have hn2 : n.val < 2 := by
    have h := n.isLt
    have hd : Module.finrank (ZMod 2) F = 2 :=
      GaloisField.finrank 2 (show 2 ≠ 0 by decide)
    exact lt_of_lt_of_eq h hd
  rcases n with ⟨n, hn'⟩
  interval_cases n
  · apply Or.inl
    ext x
    exact (congrArg (fun f : F →ₐ[ZMod 2] F => f x) hn).symm
  · apply Or.inr
    ext x
    exact (congrArg (fun f : F →ₐ[ZMod 2] F => f x) hn).symm

/-- The two field actions in the developments are literally the same map. -/
theorem fieldAction_frobenius :
    Matrix.PSL3.OuterSolvable.fieldAction F fieldFrobenius = pslFrobenius := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [fieldAction_mk, pslFrobenius_mk]
    rfl

/-- The explicit linear–coefficient normal form also supplies its cubic. -/
theorem linear_field_inverts_cubic (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hne : linearConj F m * Matrix.PSL3.OuterSolvable.fieldAction F σ ≠ 1)
    (hsq : (linearConj F m * Matrix.PSL3.OuterSolvable.fieldAction F σ) ^ 2 = 1) :
    ∃ y : PSL, orderOf y = 3 ∧
      (linearConj F m * Matrix.PSL3.OuterSolvable.fieldAction F σ) y = y⁻¹ := by
  rcases coefficient_cases σ with rfl | rfl
  · simp only [map_one, mul_one] at hne hsq ⊢
    exact inner_inverts_cubic _ (OuterPlane.FieldOccurrence.linear_involution_inner m hsq) hne hsq
  · rw [fieldAction_frobenius] at hsq ⊢
    obtain ⟨d, hd⟩ := OuterPlane.FieldOccurrence.linear_frobenius_involution_conjugate m hsq
    exact transport_inverted_cubic _ _ d hd frobenius_inverts_cubic

/-- The only branch left after the linear–field witnesses is the actual
linear–field–graph matrix action. Coverage is discharged here. -/
theorem inverted_cubic_or_graph_form (a : MulAut PSL) (hne : a ≠ 1) (hsq : a ^ 2 = 1) :
    (∃ y : PSL, orderOf y = 3 ∧ a y = y⁻¹) ∨
      ∃ (m : GL (Fin 3) F) (σ : F ≃+* F),
        a = linearConj F m * Matrix.PSL3.OuterSolvable.fieldAction F σ * graph F := by
  have hc := standard_eq_top_of_two_power_card F (m := 2) (by decide) card_F
  obtain ⟨m, σ, he | he⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization
    F field_linearConj graph_linearConj_exists field_commute_graph a (hc ▸ mem_top a)
  · apply Or.inl
    rw [he] at hne hsq ⊢
    exact linear_field_inverts_cubic m σ hne hsq
  · exact Or.inr ⟨m, σ, he⟩

/-- Final intrinsic reduction. The two outstanding inputs classify the
involutions with a graph factor; they do not assert the inverted cubic. -/
theorem involution_inverts_cubic_of_graph_conjugacy
    (hgraph : ∀ m : GL (Fin 3) F, (linearConj F m * graph F) ^ 2 = 1 →
      ∃ d : MulAut PSL, MulAut.congr d (linearConj F m * graph F) = graph F)
    (hgraphField : ∀ m : GL (Fin 3) F,
      (linearConj F m * pslFrobenius * graph F) ^ 2 = 1 →
      ∃ d : MulAut PSL, MulAut.congr d (linearConj F m * pslFrobenius * graph F) =
        pslFrobenius * graph F)
    (a : MulAut PSL) (hne : a ≠ 1) (hsq : a ^ 2 = 1) :
    ∃ y : PSL, orderOf y = 3 ∧ a y = y⁻¹ := by
  rcases inverted_cubic_or_graph_form a hne hsq with h | ⟨m, σ, he⟩
  · exact h
  · rcases coefficient_cases σ with rfl | rfl
    · simp only [map_one, mul_one] at he
      rw [he] at hsq ⊢
      obtain ⟨d, hd⟩ := hgraph m hsq
      exact transport_inverted_cubic _ _ d hd graph_inverts_cubic
    · rw [fieldAction_frobenius] at he
      rw [he] at hsq ⊢
      obtain ⟨d, hd⟩ := hgraphField m hsq
      exact transport_inverted_cubic _ _ d hd graphField_inverts_cubic

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic
