module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates
public import Theory.Representation.InvariantsBaseChange
public import Theory.Representation.EndFieldInvariants

/-!
# The adjoint endpoint of the inner SL₃ degree sieve

The repeated-word dimension formula has only one non-small pattern at or below
8r: one adjoint factor, with repetition count one. Removing the trivial tensor
factors produces its actual adjoint intertwiner, including the Frobenius twist
of the coefficient embedding. Modular invariant base change and restriction
from the Schur field then transport the literal common fixed codimension.

These are reductions. The parabolic degree bound and the strict adjoint
fixed-space estimate must still be supplied separately.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript
Lemma 4.5 and Proposition 4.7, pp.23–26; Aschbacher–Smith K.3.2, printed
pp.454–456. The tensor period is the proved one in `RepeatedModel`.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
open scoped MatrixGroups TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner

private theorem eight_mul_lt_pow {c t : ℕ} (hc : 8 ≤ c) (ht : 2 ≤ t) :
    8 * t < c ^ t := by
  induction t, ht using Nat.le_induction with
  | base =>
    have hp := Nat.pow_le_pow_left hc 2
    norm_num at hp
    omega
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem eight_mul_lt_three_pow {t : ℕ} (ht : 3 ≤ t) : 8 * t < 3 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem orbit_degree_boundary {s t a b : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hab : 0 < a + b)
    (hd : s * (3 ^ a * 8 ^ b) ^ t ≤ 8 * (s * t)) :
    (a = 1 ∧ b = 0 ∧ (t = 1 ∨ t = 2)) ∨ (a = 0 ∧ b = 1 ∧ t = 1) := by
  have h : (3 ^ a * 8 ^ b) ^ t ≤ 8 * t := by nlinarith
  by_cases hb : b = 0
  · subst b
    simp only [pow_zero, mul_one] at h
    have ha : a = 1 := by
      by_contra hn
      have ha2 : 2 ≤ a := by omega
      have hp : 9 ≤ 3 ^ a := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 3) ha2
      by_cases ht1 : t = 1
      · simp only [ht1, pow_one, mul_one] at h
        omega
      · have := eight_mul_lt_pow (by omega : 8 ≤ 3 ^ a) (by omega : 2 ≤ t)
        omega
    refine Or.inl ⟨ha, rfl, ?_⟩
    subst a
    simp only [pow_one] at h
    by_contra hn
    have := eight_mul_lt_three_pow (by omega : 3 ≤ t)
    omega
  · have hb1 : 1 ≤ b := by omega
    have hp : 8 ≤ 8 ^ b := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 8) hb1
    have hapos : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by decide)
    have hc : 8 ≤ 3 ^ a * 8 ^ b := by nlinarith
    have ht1 : t = 1 := by
      by_contra hn
      have := eight_mul_lt_pow hc (by omega : 2 ≤ t)
      omega
    subst t
    simp only [pow_one, mul_one] at h
    have ha0 : a = 0 := by
      by_contra hn
      have hp' : 3 ≤ 3 ^ a := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 3) (show 1 ≤ a by omega)
      nlinarith
    subst a
    simp only [pow_zero, one_mul] at h
    have hb' : b = 1 := by
      by_contra hn
      have hp' : 64 ≤ 8 ^ b := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 8) (show 2 ≤ b by omega)
      omega
    exact Or.inr ⟨rfl, hb', rfl⟩

private theorem trivial_word_equiv {F K : Type*} [Field F] [Field K] [CharP K 2]
    (ι : F →+* K) (w : List Factor) (ha : naturalCount w = 0) (hb : adjointCount w = 0) :
    Nonempty ((wordRep ι w).Equiv (Representation.trivial K SL(3,F) K)) := by
  induction w generalizing ι with
  | nil => exact ⟨Representation.Equiv.refl _⟩
  | cons a w ih =>
    cases a with
    | trivial =>
      have ha' : naturalCount w = 0 := by simpa [naturalCount] using ha
      have hb' : adjointCount w = 0 := by simpa [adjointCount] using hb
      obtain ⟨e⟩ := ih ((frobenius K 2).comp ι) ha' hb'
      exact ⟨(Representation.TensorProduct.lid K _).trans e⟩
    | natural => simp [naturalCount] at ha
    | dual => simp [naturalCount] at ha
    | adjoint => simp [adjointCount] at hb

private theorem single_adjoint_word_equiv {F K : Type*} [Field F] [Field K] [CharP K 2]
    (ι : F →+* K) (w : List Factor) (ha : naturalCount w = 0) (hb : adjointCount w = 1) :
    ∃ ι' : F →+* K, Nonempty ((wordRep ι w).Equiv (factorRep ι' .adjoint)) := by
  induction w generalizing ι with
  | nil => simp [adjointCount] at hb
  | cons a w ih =>
    cases a with
    | trivial =>
      have ha' : naturalCount w = 0 := by simpa [naturalCount] using ha
      have hb' : adjointCount w = 1 := by simpa [adjointCount] using hb
      obtain ⟨ι', ⟨e⟩⟩ := ih ((frobenius K 2).comp ι) ha' hb'
      exact ⟨ι', ⟨(Representation.TensorProduct.lid K _).trans e⟩⟩
    | natural => simp [naturalCount] at ha
    | dual => simp [naturalCount] at ha
    | adjoint =>
      have ha' : naturalCount w = 0 := by simpa [naturalCount] using ha
      have hb' : adjointCount w = 0 := by simpa [adjointCount] using hb
      obtain ⟨e⟩ := trivial_word_equiv ((frobenius K 2).comp ι) w ha' hb'
      exact ⟨ι, ⟨(tensorRightEquiv e).trans
        (Representation.TensorProduct.rid K (factorRep ι .adjoint))⟩⟩

private def invariantsEquiv {F G U W : Type*} [Field F] [Group G]
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    {ρ : Representation F G U} {τ : Representation F G W} (e : ρ.Equiv τ) :
    ρ.invariants ≃ₗ[F] τ.invariants where
  toFun v := ⟨e v, by
    intro g
    have h := Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap g v
    rw [v.property g] at h
    exact h.symm⟩
  invFun v := ⟨e.symm v, by
    intro g
    have h := Representation.IntertwiningMap.isIntertwining τ ρ e.symm.toIntertwiningMap g v
    rw [v.property g] at h
    exact h.symm⟩
  left_inv v := Subtype.ext (e.toLinearEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (e.toLinearEquiv.apply_symm_apply v)
  map_add' x y := Subtype.ext (map_add e (x : U) (y : U))
  map_smul' a v := Subtype.ext (map_smul e a (v : U))

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- At the weak degree boundary, the only non-small word is one adjoint factor.
Both the block and its exact repetition count are determined. -/
theorem single_adjoint_of_non_small (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (hd : Module.finrank (ZMod 2) V ≤ 8 * B.degree) :
    naturalCount M.block = 0 ∧ adjointCount M.block = 1 ∧ M.repetitions = 1 := by
  have hbound : schurDegree σ *
      (3 ^ naturalCount M.block * 8 ^ adjointCount M.block) ^ M.repetitions ≤
      8 * (schurDegree σ * M.repetitions) := by
    rw [← M.finrank_eq, ← M.field_degree]
    exact hd
  rcases orbit_degree_boundary (schurDegree_pos σ) M.repetitions_pos hp hbound with hs | ha
  · exact (hn hs).elim
  · exact ha

/-- Modular invariant base change and the actual intertwiner preserve fixed
codimension, with the original Schur-field degree as scalar multiplier. -/
theorem fixedCodim_eq_of_splitting_equiv
    {W : Type*} [AddCommGroup W] [Module (SplittingField σ) W]
    [FiniteDimensional (SplittingField σ) W]
    {τ : Representation (SplittingField σ) SL(3,B.Carrier) W}
    (e : (extendScalars (SplittingField σ) σ.endFieldRep).Equiv τ)
    (E : Subgroup SL(3,B.Carrier)) :
    fixedCodim σ E = schurDegree σ *
      Module.finrank (SplittingField σ) (W ⧸ invariants (τ.comp E.subtype)) := by
  let : Finite σ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional (SchurField σ) σ.asModule := Module.Finite.of_finite
  let eE : Representation.Equiv ((extendScalars (SplittingField σ) σ.endFieldRep).comp E.subtype)
      (τ.comp E.subtype) := Representation.Equiv.mk e.toLinearEquiv
        (fun g => e.isIntertwining' g.val)
  have hbase := finrank_invariants_extendScalars_eq_of_finite (E := SplittingField σ)
    (σ.endFieldRep.comp E.subtype)
  have hfixed : Module.finrank (ZMod 2) (fixedSpace σ E) =
      schurDegree σ * Module.finrank (SplittingField σ) (invariants (τ.comp E.subtype)) := by
    rw [fixedSpace, finrank_invariants_eq_endField_mul σ E, ← hbase]
    change schurDegree σ * _ = _
    exact congrArg (fun n => schurDegree σ * n) (invariantsEquiv eE).finrank_eq
  have htotal : Module.finrank (ZMod 2) V =
      schurDegree σ * Module.finrank (SplittingField σ) W := by
    rw [Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
      e.toLinearEquiv.finrank_eq]
    rfl
  have hbinary := fixedCodim_add_finrank σ E
  have hfield := (invariants (τ.comp E.subtype)).finrank_quotient_add_finrank
  rw [hfixed, htotal] at hbinary
  nlinarith

/-- The remaining degree-eight word is an actual trace-zero conjugation action.
Its embedding includes the position's Frobenius twist. The binary fixed
codimension is the group-field degree times the adjoint fixed codimension. -/
theorem single_adjoint_model (M : RepeatedModel B σ)
    (ha : naturalCount M.block = 0) (hb : adjointCount M.block = 1)
    (ht : M.repetitions = 1) :
    ∃ ι : B.Carrier →+* SplittingField σ,
      Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv (factorRep ι .adjoint)) ∧
      ∀ E : Subgroup SL(3,B.Carrier), fixedCodim σ E = B.degree *
        Module.finrank (SplittingField σ)
          (AdjointSpace (SplittingField σ) ⧸ invariants ((factorRep ι .adjoint).comp E.subtype)) := by
  obtain ⟨ι, ⟨e⟩⟩ := single_adjoint_word_equiv M.coefficientEmbedding M.block ha hb
  have eM : (extendScalars (SplittingField σ) σ.endFieldRep).Equiv
      (wordRep M.coefficientEmbedding M.block) := by
    have hw : (List.replicate M.repetitions M.block).flatten = M.block := by
      rw [ht]
      simp
    exact hw ▸ M.equiv
  have hn : B.degree = schurDegree σ := by simpa only [ht, mul_one] using M.field_degree
  refine ⟨ι, ⟨eM.trans e⟩, ?_⟩
  intro E
  rw [hn]
  exact fixedCodim_eq_of_splitting_equiv B σ (eM.trans e) E

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner
