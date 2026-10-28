module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PairCentralizerSplit
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FormReduction
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PRadical.NormalizerRestriction

/-!
# Elementary centralizers in the nonsingular-form reduction

For an elementary X containing a nonsingular four-group U, the existing literal
splitting C(X) = U × (C(X) ∩ K) reduces elementary-abelianness to its actual
residual factor K. An elementary C(X) is self-centralizing. If its intrinsic
form is singular, its nontrivial radical is a canonical zero-form subgroup
normalized by the whole N(X). Otherwise C(X) is the self-centralizing
nonsingular enlargement. Maximality among two-locals preserves the normalizer.

The radical application puts the canonical zero-form subgroup inside the
original radical P and proves the literal local normalizer and core identities.
The selected Figure 1/2 centralizer computations remain necessary to supply
elementary-abelianness and singularity; these reductions do not assert those
computations or classify arbitrary elementary groups of order 256.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Section 2.3,
especially Propositions 2.3.3--2.3.5 and Corollary 2.3.7, pp.492--493.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB

/-- In the nonsingular pair coordinates, only the residual intersection needs
to be checked for the elementary-centralizer calculation. -/
theorem elementary_centralizer_iff_pair_inner
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (x y : Model) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxX : x ∈ X) (hyX : y ∈ X) (hn : ¬ InnerRelated x y) :
    IsElementaryAbelian 2 (centralizer (X : Set Model)) ↔
      IsElementaryAbelian 2 (centralizer (X : Set Model) ⊓ pairInnerKernel x y : Subgroup Model) := by
  have hUX : pairGroup x y ≤ X := (closure_le _).mpr (by
    rintro z (rfl | rfl) <;> assumption)
  constructor
  · intro hC
    let := hC
    exact IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  · intro hK
    let := hK
    let : IsElementaryAbelian 2 (pairGroup x y) :=
      IsElementaryAbelian.of_injective (inclusion hUX) (inclusion_injective _)
    have hs := (elementary_pair_centralizer_decomposition X x y hx hy hxX hyX hn).2.1
    rw [hs]
    exact IsElementaryAbelian.sup_of_le_centralizer
      (inf_le_right.trans (pairInnerKernel_le_centralizer x y))

/-- An elementary full centralizer of an elementary subgroup is already
self-centralizing in the ambient matrix group. -/
theorem elementary_centralizer_self_centralizing
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    [IsElementaryAbelian 2 (centralizer (X : Set Model))] :
    centralizer (centralizer (X : Set Model) : Set Model) = centralizer (X : Set Model) :=
  le_antisymm (centralizer_le X.le_centralizer) (centralizer (X : Set Model)).le_centralizer

/-- A singular elementary centralizer supplies a canonical nontrivial zero-form
subgroup, preserved by the WHOLE original normalizer. -/
theorem singular_elementary_centralizer_reduction
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    [IsElementaryAbelian 2 (centralizer (X : Set Model))]
    (hsing : ¬ (intrinsicElementaryForm (centralizer (X : Set Model))).Nondegenerate) :
    formRadical (centralizer (X : Set Model)) ≠ ⊥ ∧
      intrinsicElementaryForm (formRadical (centralizer (X : Set Model))) = 0 ∧
      normalizer (X : Set Model) ≤
        normalizer (formRadical (centralizer (X : Set Model)) : Set Model) :=
  ⟨fun h => hsing ((formRadical_eq_bot_iff _).mp h), formRadical_form_zero _,
    (normalizer_le_normalizer_centralizer X).trans (normalizer_le_formRadical_normalizer _)⟩

/-- The Section 2.3 reduction once the literal centralizer is elementary:
maximal two-local normalizers either admit a zero-form witness or are the
normalizer of this same self-centralizing nonsingular group. -/
theorem maximal_elementary_centralizer_reduction
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hX : X ≠ ⊥)
    [IsElementaryAbelian 2 (centralizer (X : Set Model))]
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ centralizer (X : Set Model) ∧
      ∃ _hY : IsElementaryAbelian 2 Y,
        intrinsicElementaryForm Y = 0 ∧ normalizer (X : Set Model) = normalizer (Y : Set Model)) ∨
    (centralizer (centralizer (X : Set Model) : Set Model) = centralizer (X : Set Model) ∧
      (intrinsicElementaryForm (centralizer (X : Set Model))).Nondegenerate ∧
      normalizer (X : Set Model) = normalizer (centralizer (X : Set Model) : Set Model)) := by
  by_cases hnon : (intrinsicElementaryForm (centralizer (X : Set Model))).Nondegenerate
  · right
    have hC : centralizer (X : Set Model) ≠ ⊥ := fun h => hX (eq_bot_iff.mpr (h ▸ X.le_centralizer))
    exact ⟨elementary_centralizer_self_centralizing X, hnon,
      hM.eq_of_le ⟨_,hC,IsElementaryAbelian.isPGroup 2 _,rfl⟩
        (normalizer_le_normalizer_centralizer X)⟩
  · obtain ⟨hne,hzero,hnorm⟩ := singular_elementary_centralizer_reduction X hnon
    exact Or.inl ⟨_,hne,formRadical_le _,inferInstance,hzero,
      hM.eq_of_le ⟨_,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩ hnorm⟩

/-- The singular elementary-centralizer branch at an actual radical. The
canonical zero-form subgroup lies in P by radical saturation. -/
theorem radical_local_of_singular_elementary_centralizer
    (P X : Subgroup Model) (hP : P.IsPRadical 2) [IsElementaryAbelian 2 X]
    [IsElementaryAbelian 2 (centralizer (X : Set Model))]
    (hsing : ¬ (intrinsicElementaryForm (centralizer (X : Set Model))).Nondegenerate)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    let Y := formRadical (centralizer (X : Set Model))
    let M := normalizer (Y : Set Model)
    Y ≠ ⊥ ∧ intrinsicElementaryForm Y = 0 ∧ Y ≤ P ∧ IsTwoLocal M ∧
      normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  dsimp only
  let Y := formRadical (centralizer (X : Set Model))
  let M := normalizer (Y : Set Model)
  obtain ⟨hY,hzero,hnorm⟩ := singular_elementary_centralizer_reduction X hsing
  have hNM : normalizer (P : Set Model) ≤ M := hNX.trans hnorm
  have hPM := P.le_normalizer.trans hNM
  have hYP : Y ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Y hP.isPGroup (IsElementaryAbelian.isPGroup 2 Y) hP.2.le hNM
  have hN := hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hN
  refine ⟨hY,hzero,hYP,⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩,hNM,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hcore,map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover
