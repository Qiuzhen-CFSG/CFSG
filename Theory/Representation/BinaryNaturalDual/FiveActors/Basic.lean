module

public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.FlagTypes
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The actual degree-five actors and marked radical

The actor group is Aut(GL₅(2)), with its actual inner subgroup. The radical
actor is the image of the block-unipotent radical under the faithful inner
embedding. The standard complete-flag Sylow preserves the marked three-space;
the radical is also the image of the intrinsic two-core of its parabolic.

These definitions are shared by the actor classification and the
natural-plus-dual module calculations. They make no classification assumption.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.2(3),
printed pp.390–391 (PDF pp.401–402).
-/

@[expose] public section

open BinaryLinear BinaryLinear.OuterCyclic
open BinaryLinear.FiveFlagGeometry
namespace BinaryNaturalDual.FiveActors

abbrev X := BinaryLinear.OuterCyclic.Space 5
abbrev G := LinearGroup 5
abbrev M := MulAut G
abbrev L : Subgroup M := MulAut.innerSubgroup G

instance : Finite G :=
  Finite.of_injective (fun g : G => (g : X → X)) DFunLike.coe_injective

theorem center_eq_bot : Subgroup.center G = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h := ((Subgroup.centerCongr (slEquivLinear 5)).symm ⟨x, hx⟩).property
  change (slEquivLinear 5).symm x ∈ Subgroup.center _ at h
  rw [binary_center_eq_bot (by decide : 0 < 5), Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr ((slEquivLinear 5).symm.map_eq_one_iff.mp h)

noncomputable def innerEquiv : G ≃* L :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot center_eq_bot)

def radicalActor (U : Submodule (ZMod 2) X) : Subgroup M :=
  (radical U).map MulAut.conj

noncomputable def U₀ : Submodule (ZMod 2) X :=
  flagSpace SylowOvergroups.standardBasis 2

noncomputable def A₀ : Subgroup M := radicalActor U₀

theorem finrank_U₀ : Module.finrank (ZMod 2) U₀ = 3 :=
  finrank_flagSpace _ _

theorem standardSylow_preserves_U₀ :
    (SylowOvergroups.standardSylow : Subgroup G) ≤ parabolic U₀ := by
  intro g hg
  exact (mem_flagStabilizer_iff _ _ _).mp hg 2 (Set.mem_univ _)

theorem radicalActor_le_inner (U : Submodule (ZMod 2) X) : radicalActor U ≤ L := by
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

theorem radicalActor_eq_map_twoCore (U : Submodule (ZMod 2) X) :
    radicalActor U = (pCore 2 (parabolic U)).map
      ((MulAut.conj : G →* M).comp (parabolic U).subtype) := by
  rw [← Subgroup.map_map, SmallParabolicLevi.map_twoCore_eq_radical]
  rfl

end BinaryNaturalDual.FiveActors
