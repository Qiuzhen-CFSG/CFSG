module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.Inputs
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Action

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.LargePrimeSylow

/-!
# The literal Sylow image in the doubled action quotient

Restrict the ambient Sylow to the component normalizer and map it through the
actual action quotient followed by the supplied full model isomorphism. Its
image is a Sylow of the full automorphism model. Set-product permutability
survives this restriction and image. The binary model calculation makes the
image of every permuting p-subgroup with p>3 trivial; the kernel is precisely
the centralizer of the original chosen orbit.

Source: Aschbacher--Smith, 12.1.9, printed pp.793--794.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory BinaryNaturalDual BinaryLinear.OuterCyclic
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

/-- The supplied full model isomorphism composed with the literal action quotient. -/
noncomputable def modelProjection : normalizer (L : Set G) →* MulAut (LinearGroup n) :=
  B.full.toMonoidHom.comp B.actionProjection

omit [Finite G] in
theorem modelProjection_surjective : Function.Surjective B.modelProjection :=
  B.full.surjective.comp B.actionProjection_surjective

/-- The image of the original ambient Sylow in the full automorphism model. -/
noncomputable def modelSylow (hT : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Sylow 2 (MulAut (LinearGroup n)) :=
  (T.subtype hT).mapSurjective B.modelProjection_surjective

/-- This model Sylow is the literal image of the ambient Sylow restriction. -/
theorem modelSylow_coe (hT : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (B.modelSylow hT : Subgroup (MulAut (LinearGroup n))) =
      ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).map B.modelProjection := rfl

omit [Finite G] in
/-- The model projection kills exactly the centralizer of the chosen orbit. -/
theorem modelProjection_ker : B.modelProjection.ker =
    (centralizer (componentOrbit V (T : Subgroup G) : Set G)).subgroupOf
      (normalizer (L : Set G)) := by
  ext x
  change B.full (B.actionProjection x) = 1 ↔ _
  rw [← map_one B.full, B.full.injective.eq_iff]
  change (x : normalizer (L : Set G) ⧸ (normalizerAction T L V B.orbit_eq).ker) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, normalizerAction_ker]

include B in
private theorem largePrimeSylowAction_of_model (hT : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : ∀ S : Sylow 2 (MulAut (LinearGroup n)), ∀ p : ℕ, p.Prime → 3 < p →
      ∀ Y : Subgroup (MulAut (LinearGroup n)), IsPGroup p Y →
      (Y : Set (MulAut (LinearGroup n))) * (S : Set (MulAut (LinearGroup n))) =
        (S : Set (MulAut (LinearGroup n))) * (Y : Set (MulAut (LinearGroup n))) → Y = ⊥) :
    LargePrimeSylowAction (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) T := by
  intro p hp hp3 X hX hXM hperm
  let M := normalizer (L : Set G)
  let f := B.modelProjection
  have hf : Function.Surjective f := B.modelProjection_surjective
  let S₀ := T.subtype hT
  let S := S₀.mapSurjective hf
  let X₀ := X.subgroupOf M
  have hX₀ : IsPGroup p X₀ := hX.of_injective
    (subgroupOfEquivOfLe hXM).toMonoidHom (subgroupOfEquivOfLe hXM).injective
  have hximage : M.subtype '' (X₀ : Set M) = (X : Set G) := by
    exact congrArg (fun H : Subgroup G => (H : Set G)) (map_subgroupOf_eq_of_le hXM)
  have hsimage : M.subtype '' (S₀ : Set M) = (T : Set G) := by
    exact congrArg (fun H : Subgroup G => (H : Set G)) (map_subgroupOf_eq_of_le hT)
  have hperm₀ : (X₀ : Set M) * (S₀ : Set M) = (S₀ : Set M) * (X₀ : Set M) := by
    apply (Set.image_injective.mpr M.subtype_injective)
    rw [Set.image_mul, Set.image_mul, hximage, hsimage]
    exact hperm
  have hpimage :
      (X₀.map f : Set (MulAut (LinearGroup n))) * (S : Set (MulAut (LinearGroup n))) =
        (S : Set (MulAut (LinearGroup n))) * (X₀.map f : Set (MulAut (LinearGroup n))) := by
    change f '' (X₀ : Set M) * f '' (S₀ : Set M) = f '' (S₀ : Set M) * f '' (X₀ : Set M)
    rw [← Set.image_mul, ← Set.image_mul, hperm₀]
  have hbot := hmodel S p hp hp3 (X₀.map f) (hX₀.map f) hpimage
  intro x hx
  have he : f ⟨x,hXM hx⟩ = 1 := mem_bot.mp
    (hbot ▸ (mem_map_of_mem f (show (⟨x,hXM hx⟩ : M) ∈ X₀ from hx)))
  have hk : (⟨x, hXM hx⟩ : M) ∈ B.modelProjection.ker := he
  rwa [B.modelProjection_ker] at hk

include B in
/-- The large-prime action input of 12.1.9, for the original ambient Sylow,
normalizer, and chosen component orbit. -/
theorem largePrimeSylowAction (hT : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    LargePrimeSylowAction (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) T := by
  apply B.largePrimeSylowAction_of_model hT
  intro S p hp hp3 Y hY hperm
  exact ModelOrbits.AutomorphismModel.permutable_prime_eq_bot B.degree S hp hp3 Y hY hperm

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
