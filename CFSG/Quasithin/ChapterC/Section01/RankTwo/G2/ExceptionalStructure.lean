module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.ExceptionalInput
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Initial structure for the exceptional G₂ MS pair

The actual root-eight preimage is a two-group containing the ambient two-core.
The component is the two-residual of the original generated group and hence
normal there. MS3 then makes the orbit of the radical's central omega faithful
modulo the two-core. The whole central omega layer has the same kernel and
is an FF module for the literal quotient action. No odd-index-radical or
whole-core block conclusion is assumed.

These are the original-group inputs to the exceptional C.1.32 reconstruction,
applied to L Baum(R₁) by OriginalUnitaryNoncentrality.PushingUp.
Source: AS C.1.31(MS2)(b), C.1.32, pp.135–136; MS93 (2.2), (3.2).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
namespace Input
variable (h : Input κ L R)
include h

/-- The literal quotient map with the prescribed full G₂ image. -/
noncomputable def projection : G →* Atlas.G2.Model (ZMod 2) :=
  h.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))

omit [Finite G] in
theorem projection_surjective : Function.Surjective h.projection :=
  h.quotient.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem projection_kernel : h.projection.ker = pCore 2 G := by
  ext g
  change h.quotient (QuotientGroup.mk' (pCore 2 G) g) = 1 ↔ _
  rw [←h.quotient.map_one,h.quotient.injective.eq_iff]
  exact QuotientGroup.eq_one_iff g

omit [Finite G] in
theorem radical_two_group : IsPGroup 2 R := by
  rw [h.radical]
  exact (IsElementaryAbelian.isPGroup (p := 2) (G := Atlas.G2.BinaryCore.elementary)).comap_of_ker_isPGroup
    h.projection (h.projection_kernel.symm ▸ pCore_isPGroup)

omit [Finite G] in
theorem core_le_radical : pCore 2 G ≤ R := by
  rw [h.radical]
  exact h.projection_kernel.ge.trans (Subgroup.ker_le_comap _ _)

theorem component_residual : pResidual 2 G = L :=
  MSCentralOrbit.component_eq_residual L R h.component h.radical_two_group h.product

theorem component_normal : L.Normal := by
  rw [←h.component_residual]
  infer_instance

theorem component_twoPerfect : IsPPerfect 2 L := by
  rw [←h.component_residual]
  exact isPPerfect_pResidual 2

theorem core_self_centralizing : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
  rw [←h.fitting]
  exact centralizer_generalizedFitting_le G

theorem radical_ne_bot : R ≠ ⊥ := by
  intro hz
  have hq : pCore 2 G = ⊥ := le_bot_iff.mp (hz ▸ h.core_le_radical)
  have hc := h.core_self_centralizing
  rw [hq] at hc
  have htop : (⊤ : Subgroup G) ≤ (⊥ : Subgroup G) := by
    intro x _
    apply hc
    intro y hy
    have hy' : y = 1 := hy
    rw [hy',one_mul,mul_one]
  let : Group.IsSolvable G := Group.isSolvable_of_top_eq_bot G (le_bot_iff.mp htop)
  exact h.component.not_isSolvable inferInstance

/-- MS3 makes the original omega orbit faithful on the actual core quotient. -/
theorem omegaOrbit_centralizer :
    centralizer (MSCentralOrbit.omegaOrbit R : Set G) = pCore 2 G := by
  let := h.component_normal
  let := Atlas.G2.isSimple_commutator_binary
  let := h.componentQuotient.isSimpleGroup
  exact MSCentralOrbit.omegaOrbit_centralizer L R h.radical_two_group h.radical_ne_bot
    h.core_le_radical h.core_self_centralizing h.product h.characteristic

theorem centralOmega_centralizer :
    centralizer (omegaCenterIn (pCore 2 G) : Set G) = pCore 2 G :=
  MSCentralOrbit.centralOmega_centralizer R h.core_le_radical h.core_self_centralizing
    h.omegaOrbit_centralizer

noncomputable def centralOmegaAction :
    Representation (ZMod 2) (G ⧸ pCore 2 G) (Additive (omegaCenterIn (pCore 2 G))) :=
  Representation.NormalElementaryQuotient.representation _ (QuotientGroup.mk' (pCore 2 G))
    (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
      h.centralOmega_centralizer.symm)

theorem centralOmegaAction_faithful : Function.Injective h.centralOmegaAction :=
  Representation.NormalElementaryQuotient.representation_injective _ _ _ _

theorem centralOmegaAction_apply (g : G) (v : Additive (omegaCenterIn (pCore 2 G))) :
    ((h.centralOmegaAction (QuotientGroup.mk' (pCore 2 G) g) v).toMul : G) =
      g * (v.toMul : G) * g⁻¹ :=
  Representation.NormalElementaryQuotient.representation_apply _ _ _ _ g v

/-- A genuine FF offender acts on the full central omega layer in MS2(b). -/
theorem centralOmega_FF : Representation.BinaryOffender.IsFFModule h.centralOmegaAction :=
  MSCentralOrbit.centralOmega_isFFModule R h.characteristic h.radical_two_group
    h.radical_ne_bot h.core_le_radical h.core_self_centralizing h.omegaOrbit_centralizer
    (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

end Input
end CFSG.Quasithin.ChapterC.G2Exceptional
