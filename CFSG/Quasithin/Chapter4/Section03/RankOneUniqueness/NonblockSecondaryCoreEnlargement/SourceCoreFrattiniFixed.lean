module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreFixed

/-!
# The literal component Frattini fixed-point bound

The mapped intrinsic two-core is identified with the component core inside the
ambient root normalizer.  Its quotient by the intrinsic Frattini subgroup is
therefore the actual component Frattini quotient, with the same cubic action.
The general sixteen-fixed-point bound applies to this literal quotient.
-/

public noncomputable section
open Subgroup
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
attribute [local instance] SecondaryActionData.normal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
set_option backward.isDefEq.respectTransparency false

/-- The actual Frattini quotient of the component has at most sixteen fixed
points under the source cubic. -/
theorem component_frattini_fixed_card_le (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2) (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hX : X ≤ (K c).coreCenterIn 2) (hXr : X ≤ rootNormalizer c)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    let : MulDistribMulAction X (Frattini s.component) :=
      MulDistribMulAction.compHom _ ((coreAction s.component).comp (inclusion hXr))
    Nat.card (FixedPoints.subgroup X (Frattini s.component)) ≤ 16 := by
  let : MulDistribMulAction X (Frattini s.component) :=
    MulDistribMulAction.compHom _ ((coreAction s.component).comp (inclusion hXr))
  let P := (Core s.component).map (rootNormalizer c).subtype
  let j : Core s.component ≃* P :=
    (Core s.component).equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective
  let f : P →* Frattini s.component :=
    (QuotientGroup.mk' (frattini (Core s.component))).comp j.symm.toMonoidHom
  let : Normalizes X P := ⟨hXr.trans (by
    have hh := (Core s.component).le_normalizer_map (rootNormalizer c).subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh)⟩
  apply RootCoordinates.cubic_component_section_fixed_card_le m D s X hX3 hX hfix P le_rfl f
    ((QuotientGroup.mk'_surjective _).comp j.symm.surjective)
  intro x a
  change QuotientGroup.mk' _ (j.symm (x • a)) =
    coreAction s.component (inclusion hXr x) (QuotientGroup.mk' _ (j.symm a))
  rw [coreAction_eq, normalQuotientAction_apply_mk]
  congr 1
  apply j.injective
  rw [j.apply_symm_apply]
  apply Subtype.ext
  have ha := congrArg Subtype.val (j.apply_symm_apply a)
  change (x : G) * (a : G) * (x : G)⁻¹ =
    (x : G) * ((j.symm a : Core s.component) : G) * (x : G)⁻¹
  exact congrArg (fun y : G => (x : G) * y * (x : G)⁻¹) ha.symm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
