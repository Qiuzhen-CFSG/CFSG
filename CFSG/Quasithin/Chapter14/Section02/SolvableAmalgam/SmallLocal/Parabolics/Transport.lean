module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics.G2
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics.M12
public import Theory.GroupAction.MarkedParabolicTransport

/-!
# Concrete elementary-eight witnesses in an isomorphic parabolic pair

For each full small model, transport V and E through the second parabolic.
Compatibility on the whole common Sylow subgroup puts the resulting E inside
the actual O₂(H') of the first parabolic. It remains elementary of order eight
and normal in A', and an actual element of O²(A') moves the transported z.
The source identifications of Z and V and the full first-residual actions are
re-exported from the two model interfaces.

Thus the elementary-eight inputs in Aschbacher–Smith, Lemma 14.2.21, printed
p.988, apply to an isomorphism of the parabolic pair; no ambient recognition
or equality H = Mc is assumed here.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics

section G2
open Atlas.G2 Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair

/-- The G₂(2) concrete witnesses in any compatibly isomorphic parabolic pair. -/
public theorem g2_elementary_pair_transport {G : Type*} [Group G]
    (H' A' : Subgroup G) (eH : firstParabolic ≃* H') (eA : secondParabolic ≃* A')
    (hcompat : ∀ t : (commonSylow : Subgroup (Model (ZMod 2))),
      (eH ⟨t, commonSylow_le_first t.property⟩ : G) =
        (eA ⟨t, commonSylow_le_second t.property⟩ : G)) :
    let V' := ((natural.subgroupOf secondParabolic).map eA.toMonoidHom).map A'.subtype
    let E' := ((elementary.subgroupOf secondParabolic).map eA.toMonoidHom).map A'.subtype
    let z' := (eA ⟨z, elementary_le_secondParabolic z_mem_elementary⟩ : G)
    V' ≤ E' ∧ E' ≤ H'.pCoreIn 2 ∧ E' ≤ A' ∧ (E'.subgroupOf A').Normal ∧
      IsElementaryAbelian 2 E' ∧ Nat.card E' = 8 ∧ z' ∈ E' ∧
      ∃ y' : A', y' ∈ pResidual 2 A' ∧
        (y' : G) * z' * (y' : G)⁻¹ ≠ z' := by
  apply Subgroup.pair_elementary_eight_transport
    firstParabolic secondParabolic commonSylow natural elementary H' A'
    commonSylow_le_first commonSylow_le_second eH eA hcompat
    natural_le_elementary (elementary_le_core.trans core_le_unipotent)
    (by rw [firstParabolic_pCore]; exact elementary_le_core)
    card_elementary z z_mem_elementary ⟨movingActor, movingActor_mem⟩
    movingActor_residual movingActor_moves

/-- The derived pair also transports all markings of its actual first core
compatibly through either parabolic, using the entire restricted overlap. -/
public theorem g2_derived_marked_images_compatible {G : Type*} [Group G]
    (H' A' : Subgroup G) (eH : derivedFirst ≃* H') (eA : derivedSecond ≃* A')
    (hcompat : ∀ t : (derivedFirst ⊓ derivedSecond : Subgroup DerivedModel),
      (eH ⟨t, t.property.1⟩ : G) = (eA ⟨t, t.property.2⟩ : G))
    (D : Subgroup DerivedModel) (hD : D ≤ derivedFirst.pCoreIn 2) :
    ((D.subgroupOf derivedFirst).map eH.toMonoidHom).map H'.subtype =
      ((D.subgroupOf derivedSecond).map eA.toMonoidHom).map A'.subtype := by
  apply Subgroup.pair_map_eq_of_compatible derivedFirst derivedSecond
    (derivedFirst ⊓ derivedSecond) H' A' inf_le_left inf_le_right eH eA hcompat D
  rw [derived_parabolic_intersection_in_model, ← derivedFirstSylow_map_subtype]
  exact hD.trans (Subgroup.pCoreIn_le_sylow derivedFirst derivedFirstSylow)

end G2

section M12
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair

/-- The M₁₂ concrete witnesses in any compatibly isomorphic parabolic pair. -/
public theorem m12_elementary_pair_transport {G : Type*} [Group G]
    (H' A' : Subgroup G) (eH : firstParabolic ≃* H') (eA : secondParabolic ≃* A')
    (hcompat : ∀ t : sylowCandidate,
      (eH ⟨t, t.property.1⟩ : G) = (eA ⟨t, t.property.2⟩ : G)) :
    let V' := ((natural.subgroupOf secondParabolic).map eA.toMonoidHom).map A'.subtype
    let E' := ((elementary.subgroupOf secondParabolic).map eA.toMonoidHom).map A'.subtype
    let z' := (eA ⟨z, elementary_le_secondParabolic
      (natural_le_elementary z_mem_natural)⟩ : G)
    V' ≤ E' ∧ E' ≤ H'.pCoreIn 2 ∧ E' ≤ A' ∧ (E'.subgroupOf A').Normal ∧
      IsElementaryAbelian 2 E' ∧ Nat.card E' = 8 ∧ z' ∈ E' ∧
      ∃ y' : A', y' ∈ pResidual 2 A' ∧
        (y' : G) * z' * (y' : G)⁻¹ ≠ z' := by
  apply Subgroup.pair_elementary_eight_transport
    firstParabolic secondParabolic sylowCandidate natural elementary H' A'
    inf_le_left inf_le_right eH eA hcompat natural_le_elementary
    elementary_le_sylowCandidate
    (by change elementary ≤ (pCore 2 firstParabolic).map firstParabolic.subtype
        rw [mapped_pCore_eq_core]; exact elementary_le_core)
    card_elementary z (natural_le_elementary z_mem_natural)
    ⟨movingActor, movingActor_mem⟩ movingActor_residual movingActor_moves

end M12
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics
