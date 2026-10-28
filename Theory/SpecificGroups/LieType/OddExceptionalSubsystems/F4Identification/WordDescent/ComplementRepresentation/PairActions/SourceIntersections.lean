module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Orthogonality
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords
public import Theory.SpecificGroups.LieType.F4RootSL2.Elementary
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.RouteComparison

/-!
# Trivial intersections of disconnected F4 rank-one subgroups

The repeated-node subgroups are the images of the original signed-root words
in the literal F4 matrix cover. For pairs (0, 2) and (0, 3), the roots e₁+e₂ and
e₁+e₃ span a natural module for the existing faithful node-zero SL₂ map.
Both signed curves at nodes two and three fix these vectors: the shifted
vectors are not roots, as their squared norms show. Integral factorial
cancellation proves vanishing of the higher divided powers before reduction
modulo the characteristic. Thus the full rank-one subgroups fix the string,
and an intersection element has identity SL₂ matrix.

For pair (1, 3), the Tits word n₁n₀ carries α₁ to α₀. Integral route comparison
transports each signed curve, retaining its parameter sign in every degree.
The word centralizes the node-three subgroup by the established disconnected
commutation, reducing its intersection to pair (0, 3).

This proves the source-intersection input of `pairActionsOfAdjacent` and
applies it to `disconnectedProduct` and `disconnectedPairActionOfDisjoint`.
All calculations hold over every field, including F3. No universal-version
hypothesis or global F4 identification is used.

Source: GLS3 §2.6, Proposition 2.6.2(a), (d), the common-lattice subsystem
construction (`refs/KGroup/GLS3/chapter2.tex`); the exceptional inclusions
used in Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues
open ExceptionalSplit.F4RootSL2
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : DecidableEq Basis := fun a b => instDecidableEqSum a b
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg

private lemma divided_column_zero {B : Type*} [Fintype B] [DecidableEq B]
    (A D : Matrix B B ℤ) (n : ℕ) (hn : n ≠ 0)
    (hpow : A ^ n = n.factorial • D) (c : B)
    (hc : A *ᵥ Pi.single c 1 = 0) : ∀ r, D r c = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hz : A ^ (m + 1) *ᵥ Pi.single c 1 = 0 := by
    rw [pow_succ, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  rw [hpow, Matrix.smul_mulVec] at hz
  intro r
  have h := congrFun hz r
  simp only [Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    nsmul_eq_mul, Pi.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast (m + 1).factorial_ne_zero)

private lemma string_lattice (r : Fin 2) :
    latticeEquiv (.inr (.inl (r, 3))) = Sum.inr (root (if r = 0 then 11 else 15)) := by
  fin_cases r <;> rfl

private lemma string_linear_zero (i : Fin 4) (hi : i = 2 ∨ i = 3) (r : Fin 2) :
    eMatrix (sourceIndex i) *ᵥ v (b := typeF4RootPairing_base)
      (root (if r = 0 then 11 else 15)) = 0 ∧
    fMatrix (sourceIndex i) *ᵥ v (b := typeF4RootPairing_base)
      (root (if r = 0 then 11 else 15)) = 0 := by
  have hn : root (if r = 0 then 11 else 15) ≠ -(sourceIndex i : typeF4Roots) := by
    intro h
    have hh := congrArg typeF4RootPairing.root h
    rw [root_neg_value] at hh
    have hh0 := congrFun hh 0
    rcases hi with rfl | rfl <;> fin_cases r <;>
      norm_num [sourceIndex, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, root, realCoord, coord, typeF4RootPairing_root] at hh0
  have hs : root (if r = 0 then 11 else 15) ≠ (sourceIndex i : typeF4Roots) := by
    intro h
    have hh0 := congrArg (fun q : typeF4Roots => q.val 0) h
    rcases hi with rfl | rfl <;> fin_cases r <;>
      norm_num [sourceIndex, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, root, realCoord, coord] at hh0
  constructor
  · apply eMatrix_mulVec_v_zero hn
    apply not_root_of_norm
    all_goals rcases hi with rfl | rfl <;> fin_cases r <;>
      norm_num [sourceIndex, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, root, realCoord, coord, dot, Fin.sum_univ_succ,
        typeF4RootPairing_root]
  · apply fMatrix_mulVec_v_zero hs
    apply not_root_of_norm
    all_goals rcases hi with rfl | rfl <;> fin_cases r <;>
      norm_num [sourceIndex, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, root, realCoord, coord, dot, Fin.sum_univ_succ,
        typeF4RootPairing_root]

variable (F : Type*) [Field F]
private lemma string_fixed_generator (i : Fin 4) (hi : i = 2 ∨ i = 3)
    (s : Bool) (t : F) (r : Fin 2) :
    (coverSimple F s i t).val.val *ᵥ
      Pi.single (latticeEquiv (.inr (.inl (r, 3)))) 1 =
        Pi.single (latticeEquiv (.inr (.inl (r, 3)))) 1 := by
  rw [string_lattice, coverSimple_val]
  obtain ⟨he, hf⟩ := string_linear_zero i hi r
  have hE (n : ℕ) (hn : n ≠ 0) := divided_column_zero _ _ n hn
    (eMatrix_pow_eq_factorial_smul (sourceIndex i) n) _ he
  have hF (n : ℕ) (hn : n ≠ 0) := divided_column_zero _ _ n hn
    (fMatrix_pow_eq_factorial_smul (sourceIndex i) n) _ hf
  ext a
  cases s
  · change (negativeMatrix (sourceIndex i) t *ᵥ _) a = _
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, negativeMatrix_formula,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      hF 1 (by decide), hF 2 (by decide), hF 3 (by decide),
      Int.cast_zero, smul_zero, add_zero]
    simp [Matrix.one_apply, Pi.single_apply]
  · change (positiveMatrix (sourceIndex i) t *ᵥ _) a = _
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, positiveMatrix_formula,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      hE 1 (by decide), hE 2 (by decide), hE 3 (by decide),
      Int.cast_zero, smul_zero, add_zero]
    simp [Matrix.one_apply, Pi.single_apply]

private lemma rankOne_zero_le_range :
    pairSubgroup F 0 0 ≤ (elementaryHom (F := F)).range := by
  rw [pairSubgroup_eq_closure, Subgroup.closure_le]
  rintro _ ⟨⟨s, k, t⟩, rfl⟩
  cases s
  · exact ⟨lower t, by simp [coverSimple, pairNode]⟩
  · exact ⟨upper t, by simp [coverSimple, pairNode]⟩

private lemma string_fixed (i : Fin 4) (hi : i = 2 ∨ i = 3)
    (g : Cover F) (hg : g ∈ pairSubgroup F i i) (r : Fin 2) :
    g.val.val *ᵥ Pi.single (latticeEquiv (.inr (.inl (r, 3)))) 1 =
      Pi.single (latticeEquiv (.inr (.inl (r, 3)))) 1 := by
  obtain ⟨w, rfl⟩ := hg
  induction w using FreeGroup.induction_on with
  | C1 => simp only [map_one, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  | of a =>
    rcases a with ⟨s, k, t⟩
    simpa only [pairEvaluation_of, pairNode, ite_self] using
      string_fixed_generator F i hi s t r
  | inv_of a ha =>
    rw [map_inv]
    let g := pairEvaluation F i i (FreeGroup.of a)
    have hmul : (g⁻¹).val.val * g.val.val = (1 : Matrix Basis Basis F) :=
      congrArg (fun q : Cover F => q.val.val) (inv_mul_cancel g)
    calc
      _ = (g⁻¹).val.val *ᵥ (g.val.val *ᵥ
          Pi.single (latticeEquiv (.inr (.inl (r, 3)))) 1) := by rw [ha]
      _ = _ := by rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  | mul a b ha hb =>
    simpa only [map_mul, Subgroup.coe_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, hb] using ha

/-- The natural root string at roots e₁+e₂ and e₁+e₃ detects the whole node-zero subgroup,
whereas nodes two and three fix it pointwise. -/
private theorem rankOne_zero_disjoint (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    Disjoint (pairSubgroup F 0 0) (pairSubgroup F i i) := by
  rw [Subgroup.disjoint_def]
  intro g hg0 hgi
  obtain ⟨A, rfl⟩ := rankOne_zero_le_range F hg0
  have hA : A = 1 := by
    apply Subtype.ext
    ext r s
    have h := congrFun (string_fixed F i hi (elementaryHom A) hgi s)
      (latticeEquiv (.inr (.inl (r, 3))))
    change ((ambientHom A).val *ᵥ _) _ = _ at h
    rw [Matrix.mulVec_single_one, Matrix.col_apply, ambientHom_entry] at h
    simpa [blockMatrix, Matrix.blockDiagonal, Pi.single_apply,
      latticeEquiv.injective.eq_iff, Matrix.one_apply, eq_comm] using h
  rw [hA, map_one]

open ReeF4.WordRelations.RouteComparison
private lemma reflection_10 :
    reflectionWord (P := typeF4RootPairing) [sourceIndex 1, sourceIndex 0]
      (sourceIndex 1 : typeF4Roots) =
    reflectionWord (P := typeF4RootPairing) (b := typeF4RootPairing_base) []
      (sourceIndex 0 : typeF4Roots) := by
  have h : typeF4RootPairing.reflectionPerm (sourceIndex 0) (sourceIndex 1) =
      typeF4RootPairing.reflectionPerm (sourceIndex 1) (sourceIndex 0) := by
    apply typeF4RootPairing.root.injective
    rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_root' ℤ,
      typeF4RootPairing.reflection_apply_root' ℤ]
    have h01 : typeF4RootPairing.pairingIn ℤ (sourceIndex 0) (sourceIndex 1) = -1 :=
      typeF4RootPairing_base_cartan_apply 0 1
    have h10 : typeF4RootPairing.pairingIn ℤ (sourceIndex 1) (sourceIndex 0) = -1 :=
      typeF4RootPairing_base_cartan_apply 1 0
    rw [h01, h10]
    module
  simp only [reflectionWord, h, typeF4RootPairing.reflectionPerm_self]

private lemma signed_transport (s : Bool) : ∃ e : ℤ, ∀ n : ℕ,
    transportedMatrix [sourceIndex 1, sourceIndex 0]
      ((simpleFamily (b := typeF4RootPairing_base)).dividedPower (s, sourceIndex 1) n) =
        e ^ n • (simpleFamily (b := typeF4RootPairing_base)).dividedPower
          (s, sourceIndex 0) n := by
  cases s
  · obtain ⟨e, -, he⟩ := transported_fDividedPower_eq_sign_smul
      [sourceIndex 1, sourceIndex 0] [] (sourceIndex 1) (sourceIndex 0) reflection_10
    exact ⟨e, fun n => by simpa [simpleFamily, transportedMatrix, titsWord, titsWordInv_nil] using he n⟩
  · obtain ⟨e, -, he⟩ := transported_eDividedPower_eq_sign_smul
      [sourceIndex 1, sourceIndex 0] [] (sourceIndex 1) (sourceIndex 0) reflection_10
    exact ⟨e, fun n => by simpa [simpleFamily, transportedMatrix, titsWord, titsWordInv_nil] using he n⟩

private def sourceReflection (i : Fin 4) : Cover F :=
  coverSimple F true i 1 * coverSimple F false i (-1) * coverSimple F true i 1

private def sourceConjugator : Cover F := sourceReflection F 1 * sourceReflection F 0

private lemma sourceConjugator_val : (sourceConjugator F).val =
    rootCurveTitsWord (P := typeF4RootPairing) (S := F) [sourceIndex 1, sourceIndex 0] := by
  simp only [sourceConjugator, sourceReflection, Subgroup.coe_mul, coverSimple_val,
    rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  rfl

private lemma conjugate_generator (s : Bool) (t : F) : ∃ u : F,
    (MulAut.conj (sourceConjugator F)) (coverSimple F s 1 t) = coverSimple F s 0 u := by
  obtain ⟨e, he⟩ := signed_transport s
  refine ⟨e * t, ?_⟩
  apply Subtype.ext
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    sourceConjugator_val, coverSimple_val]
  apply Units.ext
  let D := simpleFamily (b := typeF4RootPairing_base)
  let C := rootCurveTitsWord (P := typeF4RootPairing) (S := F) [sourceIndex 1, sourceIndex 0]
  have h (n : ℕ) : C.val * (D.dividedPower (s, sourceIndex 1) n).map (Int.castRingHom F) * C.inv =
      (e : F) ^ n • (D.dividedPower (s, sourceIndex 0) n).map (Int.castRingHom F) := by
    dsimp only [D]
    change specializeMatrix (titsWord _) * specializeMatrix _ * specializeMatrix (titsWordInv _) = _
    rw [← specializeMatrix_transportedMatrix, he]
    ext a b
    simp only [specializeMatrix, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Int.coe_castRingHom, Int.cast_mul, Int.cast_pow]
  change C.val * (D.curve (s, sourceIndex 1) t) * C.inv = D.curve (s, sourceIndex 0) (e * t)
  simp only [IntegralCubicFamily.curve, IntegralCubicFamily.coefficient, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, mul_one]
  rw [C.val_inv, h 1, h 2, h 3]
  simp only [smul_smul, pow_one, mul_pow, mul_comm]

private lemma sourceReflection_commute (i : Fin 4) (hi : DisconnectedPair i 3)
    (g : pairSubgroup F 3 3) : Commute (sourceReflection F i) (g : Cover F) := by
  have hc (s : Bool) (t : F) : Commute (coverSimple F s i t) (g : Cover F) := by
    have h := disconnected_rankOne_commute F hi (pairGenerator F i i s true t) g
    simpa only [pairGenerator_val, pairNode, ite_self] using h
  exact ((hc true 1).mul_left (hc false (-1))).mul_left (hc true 1)

private lemma conjugator_commute (g : pairSubgroup F 3 3) :
    Commute (sourceConjugator F) (g : Cover F) :=
  (sourceReflection_commute F 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) g).mul_left
    (sourceReflection_commute F 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) g)

private lemma conjugate_rankOne_one (g : Cover F) (hg : g ∈ pairSubgroup F 1 1) :
    (MulAut.conj (sourceConjugator F)) g ∈ pairSubgroup F 0 0 := by
  have hle : pairSubgroup F 1 1 ≤
      (pairSubgroup F 0 0).comap (MulAut.conj (sourceConjugator F)).toMonoidHom := by
    rw [pairSubgroup_eq_closure, Subgroup.closure_le]
    rintro _ ⟨⟨s, k, t⟩, rfl⟩
    simp only [Subgroup.mem_comap, pairNode, ite_self]
    change (MulAut.conj (sourceConjugator F)) (coverSimple F s 1 t) ∈ pairSubgroup F 0 0
    obtain ⟨u, hu⟩ := conjugate_generator F s t
    rw [hu]
    simpa only [pairGenerator_val, pairNode, ite_self] using
      (pairGenerator F 0 0 s true u).property
  exact hle hg

private theorem rankOne_one_three_disjoint :
    Disjoint (pairSubgroup F 1 1) (pairSubgroup F 3 3) := by
  rw [Subgroup.disjoint_def]
  intro g hg1 hg3
  have hc := conjugator_commute F ⟨g, hg3⟩
  have he : (MulAut.conj (sourceConjugator F)) g = g := by
    change sourceConjugator F * g * (sourceConjugator F)⁻¹ = g
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h0 := conjugate_rankOne_one F g hg1
  rw [he] at h0
  exact (Subgroup.disjoint_def.mp (rankOne_zero_disjoint F 3 (Or.inr rfl))) h0 hg3

/-- Disconnected simple rank-one subgroups have trivial intersection in the literal F4 cover.
The calculation works over every field, including F3. -/
theorem disconnected_rankOne_disjoint (i j : Fin 4) (h : DisconnectedPair i j) :
    Disjoint (pairSubgroup F i i) (pairSubgroup F j j) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rankOne_zero_disjoint F 2 (Or.inl rfl)
  · exact rankOne_zero_disjoint F 3 (Or.inr rfl)
  · exact rankOne_one_three_disjoint F

/-- The actual product of the source rank-one subgroups embeds in the cover. -/
theorem disconnectedProduct_injective_unconditional {i j : Fin 4}
    (h : DisconnectedPair i j) : Function.Injective (disconnectedProduct F h) :=
  disconnectedProduct_injective F h (disconnected_rankOne_disjoint F i j h)

/-- Discharge the source-intersection premise of the marked disconnected action. -/
def disconnectedPairAction {i j : Fin 4} (h : DisconnectedPair i j)
    (ρ : PairAction F i i) (τ : PairAction F j j) : PairAction F i j :=
  disconnectedPairActionOfDisjoint F h (disconnected_rankOne_disjoint F i j h) ρ τ

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
