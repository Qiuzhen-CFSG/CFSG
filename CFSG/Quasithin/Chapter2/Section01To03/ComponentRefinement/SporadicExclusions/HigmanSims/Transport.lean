module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.Transport.CentralCover
public import Theory.GroupTheory.ComponentLocalDirectPowerSection

/-!
# Transporting the HS seed through a central cover and a component orbit

Source: Aschbacher–Smith, 2.3.9(7), printed p.526.

The specified intrinsic geometry supplies an invariant Sylow overgroup in HS.
Its full inverse image in the quasisimple component has characteristic two
and the actual SL₃(2) two-core quotient. The conjugates of this seed under the
supplied Sylow subgroup form a central product. After retaining its full
two-core, the normal orbit base has a quotient isomorphic to a direct power
of SL₃(2); the quotient above the base is a two-group. No extension is assumed
to split, and the supplied Sylow subgroup may permute components of H.

The fixed-subgroup two-residual lifts to genuinely centralizing elements.
Together with the Sylow subgroup already in the seed, these lifts establish
the generator coverage used by `generated_of_generators` in `Reduction`.
Thus the only extra premise of the final transport theorem is the intrinsic
geometry. Its concrete construction remains the responsibility of the HS
source-theorem assembly.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The normal orbit base has the actual direct-power quotient, retaining
both its intrinsic two-core and the outer two-group quotient. -/
theorem seed_normalDirectPowerSection (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (s : IntrinsicLocalSeed (modelSylow h d) (modelAut d d.action)) :
    Nonempty (NormalDirectPowerSection 2
      (localOvergroup ((S : Subgroup H).map H.subtype) d s.localSubgroup) LinearThreeTwo) := by
  let := h.finite
  exact h.component.relative_local_adjoin_normalDirectPowerSection h.component_le
    (componentPreimage_le d s.localSubgroup) (map_subtype_le _)
    (S.isPGroup'.map H.subtype) (seed_normalized h d s)
    (seed_selfCentralizingCore h d s) (seedQuotientEquiv h d s)

/-- Conditional central-cover and component-orbit transport. All action,
centralizing-lift, characteristic-two and quotient hypotheses are discharged;
only the explicit intrinsic HS geometry remains an input. -/
theorem localGeometry_of_intrinsicGeometry (g : IntrinsicGeometry)
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .hs) :
    Nonempty (LocalGeometry ((S : Subgroup H).map H.subtype) d) := by
  let s := transportedSeed g h d
  obtain ⟨q⟩ := seed_normalDirectPowerSection h d s
  exact ⟨localGeometry_of_normalDirectPowerSection h d s q⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
