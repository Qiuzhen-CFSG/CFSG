module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.Action
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# Actual binary offenders on the block radical's omega center

Pass the conjugation homomorphism to its actual image and construct its
faithful binary representation on V = Ω₁(Z(Q)). Fixed vectors are literal
centralizers. The maximum-elementary cardinal inequality therefore gives
an FF-offender for each nontrivial maximum elementary image.

After identifying the kernel with Q, the subgroup escaping Q supplies an
FF-module. That kernel identity is an explicit hypothesis here, not an
assumed definition of the action. The rank-one Sylow recognition remains
necessary to finish the Thompson-image theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.4/10,
pp.75–77, and C.2.7, pp.145–146, used in 15.4.20, p.1164.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
open Subgroup Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)
namespace ThompsonImage
noncomputable section

abbrev intrinsicModule : Subgroup (localGroup b) :=
  (omegaModule b).subgroupOf (localGroup b)

instance intrinsicModule_normal : (intrinsicModule b).Normal :=
  normal_subgroupOf_of_le_normalizer (localGroup_normalizes_module b)

instance intrinsicModule_elementary : IsElementaryAbelian 2 (intrinsicModule b) := by
  let _ : IsElementaryAbelian 2 (omegaModule b) := omegaModule_elementary b
  exact IsElementaryAbelian.subgroupOf
    ((omegaModule_le_core b).trans (pCoreIn_le 2 (localGroup b)))

theorem action_ker_eq_centralizer :
    (action b).ker = centralizer (intrinsicModule b : Set (localGroup b)) := by
  rw [action_ker]
  ext x
  constructor
  · intro hx
    apply mem_centralizer_iff.mpr
    intro v hv
    exact Subtype.ext (mem_centralizer_iff.mp hx v hv)
  · intro hx
    apply mem_centralizer_iff.mpr
    intro v hv
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx
      ⟨v, (omegaModule_le_core b).trans (pCoreIn_le 2 (localGroup b)) hv⟩ hv)

abbrev ActionGroup := (action b).range

def actionProjection : localGroup b →* ActionGroup b := (action b).rangeRestrict

theorem actionProjection_surjective : Function.Surjective (actionProjection b) :=
  (action b).rangeRestrict_surjective

theorem actionProjection_ker :
    (actionProjection b).ker = centralizer (intrinsicModule b : Set (localGroup b)) :=
  (action b).ker_rangeRestrict.trans (action_ker_eq_centralizer b)

def representation : Representation (ZMod 2) (ActionGroup b) (Additive (intrinsicModule b)) :=
  Representation.NormalElementaryQuotient.representation (intrinsicModule b)
    (actionProjection b) (actionProjection_surjective b) (actionProjection_ker b)

theorem representation_apply (g : localGroup b) (v : Additive (intrinsicModule b)) :
    ((representation b (actionProjection b g) v).toMul : localGroup b) =
      g * (v.toMul : localGroup b) * g⁻¹ :=
  Representation.NormalElementaryQuotient.representation_apply (intrinsicModule b)
    (actionProjection b) (actionProjection_surjective b) (actionProjection_ker b) g v

theorem representation_injective : Function.Injective (representation b) :=
  Representation.NormalElementaryQuotient.representation_injective (intrinsicModule b)
    (actionProjection b) (actionProjection_surjective b) (actionProjection_ker b)

def faithfulImage (A : Subgroup G) : Subgroup (ActionGroup b) :=
  (A.subgroupOf (localGroup b)).map (actionProjection b)

theorem faithfulImage_map (A : Subgroup G) :
    (faithfulImage b A).map (action b).range.subtype = image b A := by
  rw [faithfulImage, map_map]
  rfl

theorem faithfulImage_ne_bot_iff (A : Subgroup G) :
    faithfulImage b A ≠ ⊥ ↔ image b A ≠ ⊥ := by
  rw [← faithfulImage_map b A]
  exact not_congr (Subgroup.map_eq_bot_iff_of_injective
    _ (action b).range.subtype_injective).symm

/-- The cardinal bound supplies an actual offender for the faithful action. -/
theorem maximum_isOffender (hQ : blockRadicalCore b ≤ contraryCore c)
    {A : Subgroup G} (hA : A ∈ elementaryAbelianMaxSubgroups (contraryCore c))
    (hne : image b A ≠ ⊥) :
    Representation.BinaryOffender.IsOffender (representation b) (faithfulImage b A) := by
  apply Representation.NormalElementaryQuotient.maxElementary_isOffender
    (intrinsicModule b) (actionProjection b) (actionProjection_surjective b)
    (actionProjection_ker b) ((contraryCore c).subgroupOf (localGroup b))
    (A.subgroupOf (localGroup b)) (fun _ hv => hQ (omegaModule_le_core b hv))
    (maximum_subgroupOf b hA)
  intro hle
  exact ((faithfulImage_ne_bot_iff b A).mpr hne) ((Subgroup.map_eq_bot_iff _).mpr hle)

/-- The kernel equality makes the escaping maximum subgroup an offender. -/
theorem exists_maximum_offender (hQ : blockRadicalCore b ≤ contraryCore c)
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (contraryCore c),
      image b A ≠ ⊥ ∧
      Representation.BinaryOffender.IsOffender (representation b) (faithfulImage b A) := by
  obtain ⟨A, hA, hAQ⟩ := exists_maximum_not_le_core b hQ
  have hne := (image_ne_bot_iff_of_kernel b hker (hA.1.trans le_sup_right)).mpr hAQ
  exact ⟨A, hA, hne, maximum_isOffender b hQ hA hne⟩

theorem isFFModule_of_kernel (hQ : blockRadicalCore b ≤ contraryCore c)
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    Representation.BinaryOffender.IsFFModule (representation b) := by
  obtain ⟨A, _, _, hA⟩ := exists_maximum_offender b hQ hker
  exact ⟨faithfulImage b A, hA⟩

end
end ThompsonImage
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
