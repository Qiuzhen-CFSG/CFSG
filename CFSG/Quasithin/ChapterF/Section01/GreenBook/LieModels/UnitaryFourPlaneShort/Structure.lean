module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Structure
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.OrthogonalFourMinusBinaryIrreducibility
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Shortness and residuals of the unitary-four plane factor

The concrete plane factor has elementary abelian Hermitian two-core and
quasisimple SL₂ quotient. Faithfulness of the literal quotient action makes
the core self-centralizing, hence equal to the generalized Fitting subgroup.
Binary irreducibility makes it a minimal normal subgroup. It follows that
[O₂(L₂),L₂] = O₂(L₂) and that its fixed subgroup is trivial. The perfect
quotient and the full commutator layer make L₂ perfect.

These arguments hold for every n ≥ 1, including the ground field of order two.
They discharge all shortness clauses of Aschbacher--Smith C.1.7 (printed p.123)
and the plane-factor residual assertion used in F.1.12(II) (pp.263–264).
The orthogonal natural-module identification of C.1.30 remains with the
plane-block assembly; here the group and action are the original concrete ones.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Matrix Subgroup Theory.GroupTheory
open Representation.OrthogonalFourMinus
open scoped commutatorElement MatrixGroups
variable (n : ℕ) (hn : 1 ≤ n)

instance L2_finite : Finite (L2 n hn) := by
  let : Finite (GL (Fin 4) (MatrixField n)) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveGroup n hn) := Finite.of_surjective (projection n hn)
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective _ _)
  infer_instance

/-- The Hermitian two-core is its own centralizer in the plane factor. -/
theorem L2TwoCore_centralizer :
    centralizer (pCore 2 (L2 n hn) : Set (L2 n hn)) = pCore 2 (L2 n hn) := by
  rw [← MulAut.conjNormal_ker_eq_centralizer, L2TwoCore_conjugation_ker]

/-- Characteristic two in the generalized Fitting convention. -/
theorem L2_generalizedFitting : generalizedFitting (L2 n hn) = pCore 2 (L2 n hn) :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2 (L2TwoCore_centralizer n hn).le

private theorem planeSL2_quasisimple [NeZero n] :
    IsQuasisimple (SpecialLinearGroup (Fin 2) (FiniteModel.Field n)) := by
  obtain ⟨t, ht⟩ := FiniteModel.exists_conjugation_ne n
  have ht0 : t ≠ 0 := by intro h; apply ht; simp [h]
  have htsq : t ^ 2 ≠ 1 := by
    intro h
    have ht1 : t = 1 := by
      rcases sq_eq_one_iff.mp h with he | he
      · exact he
      · simpa only [CharTwo.neg_eq] using he
    apply ht
    simp [ht1]
  exact { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top ht0 htsq⟩
          simple := ProjectiveSpecialLinearGroup.rank_two_simple' ⟨t, ht0, htsq⟩ }

/-- The genuine quotient is quasisimple even over the binary ground field. -/
theorem L2_quotient_quasisimple : IsQuasisimple (L2 n hn ⧸ pCore 2 (L2 n hn)) := by
  let : NeZero n := ⟨by omega⟩
  let := planeSL2_quasisimple n
  exact IsQuasisimple.of_mulEquiv (L2QuotientEquivSL2 n hn).symm

/-- The two-core is proper because its quotient is the nontrivial SL₂ group. -/
theorem L2TwoCore_ne_top : pCore 2 (L2 n hn) ≠ ⊤ := by
  let : IsQuasisimple (L2 n hn ⧸ pCore 2 (L2 n hn)) := L2_quotient_quasisimple n hn
  let : IsSimpleGroup ((L2 n hn ⧸ pCore 2 (L2 n hn)) ⧸
    center (L2 n hn ⧸ pCore 2 (L2 n hn))) := IsQuasisimple.simple
  let : Nontrivial (L2 n hn ⧸ pCore 2 (L2 n hn)) :=
    (QuotientGroup.mk'_surjective (center (L2 n hn ⧸ pCore 2 (L2 n hn)))).nontrivial
  exact QuotientGroup.nontrivial_iff.mp inferInstance

/-- The radical has positive rank at every positive exponent. -/
theorem L2TwoCore_ne_bot : pCore 2 (L2 n hn) ≠ ⊥ := by
  intro h
  have hc := L2TwoCore_card n hn
  have hc0 : Nat.card (pCore 2 (L2 n hn)) = 1 := by rw [h]; exact Nat.card_unique
  have hg : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  have hg' : 1 < (2 ^ n) ^ 4 := Nat.one_lt_pow (by decide) hg
  omega

/-- The radical is a minimal normal subgroup, using binary irreducibility of
its actual Hermitian conjugation action. -/
theorem L2TwoCore_normal_subgroup (N : Subgroup (L2 n hn)) (hN : N.Normal)
    (hNR : N ≤ pCore 2 (L2 n hn)) : N = ⊥ ∨ N = pCore 2 (L2 n hn) := by
  let : NeZero n := ⟨by omega⟩
  let i : Multiplicative (FiniteModel.Space n) →* L2 n hn :=
    (pCore 2 (L2 n hn)).subtype.comp (L2TwoCoreEquiv n hn).toMonoidHom
  let W := N.comap i
  have hW : ∀ A X, X ∈ W → FiniteModel.multiplicativeAction n A X ∈ W := by
    intro A X hX
    obtain ⟨g, hg⟩ := (L2QuotientEquivSL2 n hn).surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 (L2 n hn))) A
    have he : i (FiniteModel.multiplicativeAction n A X) = g * i X * g⁻¹ := by
      rw [← hg]
      exact (congrArg Subtype.val (L2TwoCoreEquiv_conj n hn g X)).symm
    change i (FiniteModel.multiplicativeAction n A X) ∈ N
    rw [he]
    exact hN.conj_mem _ hX g
  rcases FiniteModel.multiplicativeAction_irreducible n W hW with h | h
  · left
    apply N.eq_bot_iff_forall.mpr
    intro x hx
    obtain ⟨X, hX⟩ := (L2TwoCoreEquiv n hn).surjective ⟨x, hNR hx⟩
    have hi : i X = x := congrArg Subtype.val hX
    have hmem : X ∈ W := by change i X ∈ N; rwa [hi]
    rw [h, Subgroup.mem_bot] at hmem
    rw [← hi, hmem, map_one]
  · right
    apply le_antisymm hNR
    intro x hx
    obtain ⟨X, hX⟩ := (L2TwoCoreEquiv n hn).surjective ⟨x, hx⟩
    have hi : i X = x := congrArg Subtype.val hX
    have hmem : X ∈ W := by rw [h]; trivial
    change i X ∈ N at hmem
    rwa [hi] at hmem

private theorem L2TwoCore_not_le_center : ¬pCore 2 (L2 n hn) ≤ center (L2 n hn) := by
  intro h
  apply L2TwoCore_ne_top n hn
  apply top_unique
  calc
    ⊤ = centralizer (center (L2 n hn) : Set (L2 n hn)) := centralizer_center.symm
    _ ≤ centralizer (pCore 2 (L2 n hn) : Set (L2 n hn)) := centralizer_le h
    _ = pCore 2 (L2 n hn) := L2TwoCore_centralizer n hn

/-- The elementary commutator layer is the entire Hermitian radical. -/
theorem L2_blockU_eq_twoCore : ChapterC.blockU (L2 n hn) = pCore 2 (L2 n hn) := by
  rcases L2TwoCore_normal_subgroup n hn (ChapterC.blockU (L2 n hn)) inferInstance
      ChapterC.blockU_le_core with h | h
  · exact (L2TwoCore_not_le_center n hn
      (commutator_top_right_eq_bot_iff_le_center.mp h)).elim
  · exact h

theorem L2_blockU_eq_radical : ChapterC.blockU (L2 n hn) = L2Radical n hn := by
  rw [L2_blockU_eq_twoCore, L2Radical_eq_twoCore]

/-- No nontrivial radical element is fixed by the whole local group. -/
theorem L2TwoCore_inf_center : pCore 2 (L2 n hn) ⊓ center (L2 n hn) = ⊥ := by
  rcases L2TwoCore_normal_subgroup n hn (pCore 2 (L2 n hn) ⊓ center (L2 n hn))
    inferInstance inf_le_left with h | h
  · exact h
  · exact (L2TwoCore_not_le_center n hn (inf_eq_left.mp h)).elim

/-- The literal subgroup used to form the block module is trivial. -/
theorem L2_blockFixed_eq_bot : ChapterC.blockFixed (L2 n hn) = ⊥ := by
  apply (Subgroup.map_injective (ChapterC.blockU (L2 n hn)).subtype_injective)
  rw [ChapterC.blockFixed_map, Subgroup.map_bot, L2_blockU_eq_twoCore, L2TwoCore_inf_center]

/-- The strict invariant-subgroup condition of C.1.7, including nonzero module. -/
theorem L2_blockModuleIrreducible : ChapterC.BlockModuleIrreducible (L2 n hn) := by
  unfold ChapterC.BlockModuleIrreducible
  rw [L2_blockU_eq_twoCore, L2TwoCore_inf_center]
  exact ⟨bot_lt_iff_ne_bot.mpr (L2TwoCore_ne_bot n hn),
    fun N hN _ hNR => L2TwoCore_normal_subgroup n hn N hN hNR⟩

/-- The plane factor is perfect, also when the ground field has order two. -/
theorem L2_isPerfect : Group.IsPerfect (L2 n hn) := by
  let : IsQuasisimple (L2 n hn ⧸ pCore 2 (L2 n hn)) := L2_quotient_quasisimple n hn
  have hR : pCore 2 (L2 n hn) ≤ commutator (L2 n hn) := by
    rw [← L2_blockU_eq_twoCore]
    exact commutator_mono le_top le_rfl
  let q := QuotientGroup.mk' (pCore 2 (L2 n hn))
  have hm : (commutator (L2 n hn)).map q = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  constructor
  have he := congrArg (Subgroup.comap q) hm
  rw [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hR] at he
  exact he

/-- Two-perfection is a consequence of ordinary perfectness. -/
theorem L2_isPPerfect : IsPPerfect 2 (L2 n hn) := by
  let := L2_isPerfect n hn
  intro N hN hq
  let := hN
  by_contra hne
  let : Nontrivial (L2 n hn ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsNilpotent (L2 n hn ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (L2 n hn ⧸ N) inferInstance

/-- Every structural clause of shortness holds for the concrete plane factor. -/
theorem L2_isShort : ChapterC.IsShort (L2 n hn) where
  finite := inferInstance
  twoPerfect := L2_isPPerfect n hn
  fitting := L2_generalizedFitting n hn
  elementary := by rw [L2_blockU_eq_twoCore]; infer_instance
  central := by rw [L2_blockU_eq_twoCore, L2TwoCore_centralizer]
  quotient := Or.inl (L2_quotient_quasisimple n hn)
  irreducible := L2_blockModuleIrreducible n hn

/-- The solvable residual is the whole intrinsic plane factor. -/
theorem L2_solvableResidual_eq_top : solvableResidual (L2 n hn) = ⊤ := by
  let := L2_isPerfect n hn
  exact solvableResidual_eq_top

/-- In the original projective ambient group, L₂ equals its solvable residual. -/
theorem L2_solvableResidual_map :
    (solvableResidual (L2 n hn)).map (L2 n hn).subtype = L2 n hn := by
  rw [L2_solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]

/-- The actual two-residual is also the whole plane factor. -/
theorem L2_pResidual_eq_top : pResidual 2 (L2 n hn) = ⊤ :=
  (pResidual_eq_top_iff 2 (L2 n hn)).mpr (L2_isPPerfect n hn)

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
