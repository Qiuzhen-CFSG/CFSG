module

public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Models
public import Theory.GroupTheory.PCoreSurjective

/-!
# The two-core of the complementary four-letter subgroup

The concrete subgroup `pairResidual` projects onto the alternating group on
coordinates 2–5. Its kernel consists of vectors, hence has exponent two.
The displayed double transpositions generate the image of the actual Klein
four subgroup of that A₄. Pulling its two-core back through the projection
gives `pairCore`, with normality relative to `pairResidual` and the two-group
property proved separately.

Only the small permutation coordinate comparisons use finite certificates;
no enumeration of the semidirect product is involved. This calculation is
intrinsic to `pairResidual` and assumes no centralizer-residual identity.

Source: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup
namespace BinaryPermutation.SixCoreExtension
open Theory.SpecificGroups.SymmetricSix
local instance : Fintype (Equiv.Perm (Fin 6)) := fintypePerm
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance (g : Equiv.Perm (Fin 6)) : Decidable (g ∈ A) :=
  inferInstanceAs (Decidable (g.sign = 1))
local instance : Fintype A := Subtype.fintype _
local instance : Fintype ResidualPairRecognition.A := Subtype.fintype _

/-- The actual complementary A₄, embedded using the four-letter duad action. -/
def pairActorEmbedding : ResidualPairRecognition.A →* A := ResidualPairRecognition.duadHom.codRestrict _ (by
  intro a
  change (ResidualPairRecognition.duadHom a).sign = 1
  revert a
  decide +kernel)

/-- The duad embedding fixes both marked coordinates individually. -/
theorem pairActorEmbedding_fixes : ∀ a : ResidualPairRecognition.A,
    (pairActorEmbedding a).val 0 = 0 ∧ (pairActorEmbedding a).val 1 = 1 := by
  decide +kernel

/-- The complementary action retains all four-letter permutations. -/
theorem pairActorEmbedding_injective : Function.Injective pairActorEmbedding := by
  intro a b h
  exact ResidualPairRecognition.duadHom_injective (congrArg Subtype.val h)

/-- Every even actor fixing the marked coordinates comes from this A₄. -/
theorem pairActorEmbedding_covers : ∀ g : A, g.val 0 = 0 → g.val 1 = 1 →
    ∃ a : ResidualPairRecognition.A, pairActorEmbedding a = g := by
  decide +kernel



noncomputable section

/-- Restrict the literal right projection to the actual complementary A₄. -/
def pairActorProjection : pairResidual →* ResidualPairRecognition.A :=
  (MonoidHom.ofInjective pairActorEmbedding_injective).symm.toMonoidHom.comp
    ((SemidirectProduct.rightHom.comp pairResidual.subtype).codRestrict
      pairActorEmbedding.range (fun x =>
        pairActorEmbedding_covers x.val.right x.property.2.2.1 x.property.2.2.2))

/-- The A₄ projection recovers exactly the original right coordinate. -/
theorem pairActorEmbedding_projection (x : pairResidual) :
    pairActorEmbedding (pairActorProjection x) = x.val.right :=
  MonoidHom.apply_ofInjective_symm pairActorEmbedding_injective _

/-- The literal semidirect-product complement supplies every A₄ actor. -/
theorem pairActorProjection_surjective : Function.Surjective pairActorProjection := by
  intro a
  have ha := pairActorEmbedding_fixes a
  let x : pairResidual := ⟨SemidirectProduct.inr (pairActorEmbedding a),
    ⟨rfl, rfl, ha.1, ha.2⟩⟩
  refine ⟨x, pairActorEmbedding_injective ?_⟩
  rw [pairActorEmbedding_projection]
  rfl

/-- The projection kernel is precisely the vector part of `pairResidual`. -/
theorem mem_pairActorProjection_ker (x : pairResidual) :
    x ∈ pairActorProjection.ker ↔ x.val.right = 1 := by
  change pairActorProjection x = 1 ↔ _
  rw [← pairActorEmbedding_injective.eq_iff, map_one, pairActorEmbedding_projection]

/-- Binary vectors have exponent two, so the projection has two-group kernel. -/
theorem pairActorProjection_ker_isPGroup : IsPGroup 2 pairActorProjection.ker := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val ^ 2 = 1
  have hr := (mem_pairActorProjection_ker x.val).mp x.property
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    rw [square_left, hr]
    exact CharTwo.add_self_eq_zero _
  · change (x.val.val ^ 2).right = (1 : A)
    change SemidirectProduct.rightHom (x.val.val ^ 2) = 1
    rw [map_pow]
    change x.val.val.right ^ 2 = 1
    rw [hr, one_pow]

private theorem klein_image_cases : ∀ a : ResidualPairRecognition.A,
    a ∈ ResidualPairRecognition.klein →
      pairActorEmbedding a = 1 ∨ pairActorEmbedding a = kleinFirst ∨
        pairActorEmbedding a = kleinSecond ∨
          pairActorEmbedding a = kleinFirst * kleinSecond := by
  decide +kernel

private theorem klein_generators_mem_image :
    kleinFirst ∈ ResidualPairRecognition.klein.map pairActorEmbedding ∧
      kleinSecond ∈ ResidualPairRecognition.klein.map pairActorEmbedding := by
  simp only [mem_map]
  decide +kernel

/-- The two specified generators give the literal image of the A₄ Klein four. -/
theorem pairKlein_eq_map :
    pairKlein = ResidualPairRecognition.klein.map pairActorEmbedding := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact klein_generators_mem_image.1
    · rw [Set.mem_singleton_iff] at ha
      subst a
      exact klein_generators_mem_image.2
  · rintro a ⟨b, hb, rfl⟩
    have h1 : kleinFirst ∈ pairKlein := subset_closure (Set.mem_insert _ _)
    have h2 : kleinSecond ∈ pairKlein := subset_closure (Set.mem_insert_of_mem _ rfl)
    rcases klein_image_cases b hb with h | h | h | h
    · rw [h]; exact pairKlein.one_mem
    · rw [h]; exact h1
    · rw [h]; exact h2
    · rw [h]; exact pairKlein.mul_mem h1 h2

/-- Inside `pairResidual`, the concrete W:V₄ is the inverse image of V₄. -/
theorem pairCore_subgroupOf_eq_comap :
    pairCore.subgroupOf pairResidual =
      ResidualPairRecognition.klein.comap pairActorProjection := by
  ext x
  change (x.val ∈ pairResidual ∧ x.val.right ∈ pairKlein) ↔
    pairActorProjection x ∈ ResidualPairRecognition.klein
  rw [pairKlein_eq_map]
  constructor
  · rintro ⟨_, a, ha, he⟩
    have he' : a = pairActorProjection x :=
      pairActorEmbedding_injective (he.trans (pairActorEmbedding_projection x).symm)
    rwa [← he']
  · intro hx
    exact ⟨x.property, _, hx, pairActorEmbedding_projection x⟩

/-- Normality is relative to W:A₄, rather than to the whole model. -/
instance pairCore_normal : (pairCore.subgroupOf pairResidual).Normal := by
  rw [pairCore_subgroupOf_eq_comap]
  infer_instance

/-- W:V₄ is a two-group, by its vector kernel and Klein four quotient. -/
theorem pairCore_isPGroup : IsPGroup 2 pairCore := by
  have hp : IsPGroup 2 (pairCore.subgroupOf pairResidual) := by
    rw [pairCore_subgroupOf_eq_comap, ← ResidualPairRecognition.klein_core]
    exact pCore_isPGroup.comap_of_ker_isPGroup _ pairActorProjection_ker_isPGroup
  exact hp.of_equiv (subgroupOfEquivOfLe (show pairCore ≤ pairResidual from inf_le_left))

/-- The embedded two-core of the concrete W:A₄ is exactly the concrete W:V₄. -/
theorem pairResidual_pCoreIn : pairResidual.pCoreIn 2 = pairCore := by
  have he := pairActorProjection.comap_pCore_of_ker_isPGroup
    pairActorProjection_surjective pairActorProjection_ker_isPGroup
  rw [ResidualPairRecognition.klein_core, ← pairCore_subgroupOf_eq_comap] at he
  unfold pCoreIn
  rw [← he, map_subgroupOf_eq_of_le (show pairCore ≤ pairResidual from inf_le_left)]

end
end BinaryPermutation.SixCoreExtension
