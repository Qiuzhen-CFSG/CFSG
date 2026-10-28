module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.Preparation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.NaturalLayerRecognition
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator
public import Theory.Quasithin.Rank

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The natural initial module of an arbitrary small G₂ MS pair

MS3 produces an FF offender on the actual central-omega layer. Its faithful
quotient contains the self-centralizing simple component G₂(2)′. The proved
FF classification identifies the component's moved space modulo its fixed
part with the trace-zero octonions modulo scalars. Irr-plus also identifies
the moving parts of the omega orbit and the central-omega layer.

This identifies the initial module, not the entire commutator core. The
remaining MS93 (3.6) containment is consumed in `Source`.
Source: AS C.1.31--32; MS93 (2.2), (3.2)(vii), pp.857,863--866.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional
open ChapterC
namespace Reconstruction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

local notation "H" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h e

theorem initial_orbit_centralizer :
    centralizer (MSCentralOrbit.omegaOrbit T : Set H) = pCore 2 H := by
  let := relative_normal h
  let := Atlas.G2.isSimple_commutator_binary
  let := (relativeCoreEquiv h e).isSimpleGroup
  exact MSCentralOrbit.omegaOrbit_centralizer K T (edge_two_group h) (edge_ne_bot h)
    (core_le_edge h) (core_self_centralizing h) (relative_product h) (edge_characteristic h)

theorem central_omega_centralizer :
    centralizer (omegaCenterIn (pCore 2 H) : Set H) = pCore 2 H :=
  MSCentralOrbit.centralOmega_centralizer T (core_le_edge h)
    (core_self_centralizing h) (initial_orbit_centralizer h e)

def quotientComponent : Subgroup (H ⧸ pCore 2 H) := (K).map (QuotientGroup.mk' (pCore 2 H))

noncomputable def quotientComponentEquiv :
    quotientComponent (L := L) (R := R) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (cComponentTwoCoreQuotientEquiv h.component).symm.trans (relativeCoreEquiv h e)

theorem quotientComponent_card : Nat.card (quotientComponent (L := L) (R := R)) = 6048 :=
  (Nat.card_congr (quotientComponentEquiv h e).toEquiv).trans
    (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))

theorem quotientComponent_structure :
    (quotientComponent (L := L) (R := R)).Normal ∧
    IsSimpleGroup (quotientComponent (L := L) (R := R)) ∧
    IsQuasisimple (quotientComponent (L := L) (R := R)) ∧
    centralizer (quotientComponent (L := L) (R := R) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let := Atlas.G2.isSimple_commutator_binary
  let := (relativeCoreEquiv h e).isSimpleGroup
  exact (MSCentralOrbit.component_image_structure K T h.component
    (edge_two_group h) (relative_product h)).2

omit e in
theorem quotientComponent_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (quotientComponent (L := L) (R := R)) := by
  have hsq : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) :=
    ⟨fun p hp ho => by
      let _ : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
        (h.sqtk.stronglyQuasithin p hp ho), h.sqtk.isKGroup.quotient _⟩
  exact hsq.subgroup _

noncomputable def centralOmegaAction :
    Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (omegaCenterIn (pCore 2 H))) :=
  Representation.NormalElementaryQuotient.representation _ (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
      (central_omega_centralizer h e).symm)

theorem centralOmegaAction_faithful : Function.Injective (centralOmegaAction h e) :=
  Representation.NormalElementaryQuotient.representation_injective _ _ _ _

theorem centralOmegaAction_apply (g : H) (v : Additive (omegaCenterIn (pCore 2 H))) :
    ((centralOmegaAction h e (QuotientGroup.mk' (pCore 2 H) g) v).toMul : H) =
      g * (v.toMul : H) * g⁻¹ :=
  Representation.NormalElementaryQuotient.representation_apply _ _ _ _ g v

theorem central_omega_FF : Representation.BinaryOffender.IsFFModule (centralOmegaAction h e) :=
  MSCentralOrbit.centralOmega_isFFModule T (edge_characteristic h) (edge_two_group h)
    (edge_ne_bot h) (core_le_edge h) (core_self_centralizing h) (initial_orbit_centralizer h e)
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- The natural model concerns the literal moved/fixed section of the central omega layer. -/
theorem initial_moved_natural :
    let := (quotientComponent_structure h e).1
    Representation.BinaryOffender.IsIrrPlus (centralOmegaAction h e) (quotientComponent (L := L) (R := R))
      (Representation.BinaryOffender.subspaceCommutator (centralOmegaAction h e) ⊤
        (quotientComponent (L := L) (R := R))) ∧
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        ((ChapterB.QuasisimpleSource.MovedSection.ofNormal (centralOmegaAction h e)
          (quotientComponent (L := L) (R := R))).action.comp
            (quotientComponent (L := L) (R := R)).subtype)
        (Representation.g2DerivedNatural (ZMod 2))) := by
  let := (quotientComponent_structure h e).1
  let := (quotientComponent_structure h e).2.1
  let := (quotientComponent_structure h e).2.2.1
  exact RankTwo.G2.ff_card_g2_two_moved_natural _ _ (quotientComponent_card h e)
    (quotientComponent_structure h e).2.2.2 (quotientComponent_sqtk h)
    (centralOmegaAction_faithful h e) (central_omega_FF h e)

/-- MS93's initial U is the moving part of the actual central omega layer. -/
theorem initialCore_eq :
    ⁅MSCentralOrbit.omegaOrbit T,K⁆ = ⁅omegaCenterIn (pCore 2 H),K⁆ := by
  let := (quotientComponent_structure h e).1
  let := (quotientComponent_structure h e).2.2.1
  let : IsElementaryAbelian 2 (MSCentralOrbit.omegaOrbit T) :=
    MSCentralOrbit.omegaOrbit_elementary _ (core_le_edge h) (core_self_centralizing h)
  have hne : quotientComponent (L := L) (R := R) ≠ ⊥ := by
    intro hz
    have hc := quotientComponent_card h e
    rw [hz,card_bot] at hc
    omega
  exact Representation.NormalElementaryQuotient.commutator_eq_of_irrPlus
    (MSCentralOrbit.omegaOrbit T) (omegaCenterIn (pCore 2 H))
    (MSCentralOrbit.omegaOrbit_le_centralOmega _ (core_le_edge h) (core_self_centralizing h))
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (initial_orbit_centralizer h e).symm)
    ((QuotientGroup.ker_mk' _).trans (central_omega_centralizer h e).symm)
    K (quotientComponent (L := L) (R := R)) rfl hne (initial_moved_natural h e).1

end Reconstruction
end CFSG.Quasithin.ChapterC.G2Exceptional
