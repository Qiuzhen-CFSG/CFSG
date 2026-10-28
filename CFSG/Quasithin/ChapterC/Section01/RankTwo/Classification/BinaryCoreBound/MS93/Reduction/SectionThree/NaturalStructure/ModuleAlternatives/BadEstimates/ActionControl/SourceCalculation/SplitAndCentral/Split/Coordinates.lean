module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral.Split.Endpoints
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.ModuleCriterion

/-!
# The actual doubled-natural coordinates at a critical pair

The given moving isomorphism induces a linear equivalence intertwining the
literal conjugation action, with the original marking on both summands.
It transports the critical image of order four to the concrete doubled
natural representation. Its fixed codimension is at most two, by restriction
from the actual X layer and the proved critical displacement index.

The entire stabilizer displacement of X is U, so the critical commutator
lies in U at the endpoint. The pointwise-fixer calculation in the concrete
representation, and its final source-(3.3) quotient assembly, remain separate.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.2)(iii), p.863, and (3.3), pp.866–868.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The full stabilizer displacement of X is exactly the moving summand. -/
theorem X_commutator_eq_U (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) : ⁅X R a, stabilizer R a⁆ = U R a := by
  have he : ⁅X R a, Ltilde R a⁆ = ⁅X R a, stabilizer R a⁆ :=
    commutator_eq_of_centralizing_sup
      (by rw [sup_comm]; exact source.local_generation a ha)
      (Q_le_centralizer_X R a) ((Ltilde_le_stabilizer a).trans (X_normalized R a))
  rw [← he, splitDouble_X_eq_Z source geometry hb hmodel a ha]
  rfl

/-- The actual critical commutator lies inside the moving summand at the endpoint. -/
theorem critical_commutator_le_U (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅X R a, X R a'⁆ ≤ U R a' := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl (critical_X_le_stabilizer source geometry hb a ha a' hc)).trans
    (X_commutator_eq_U source geometry hb hmodel a'
      (critical_endpoint_color R a ha _ hc)).le

/-- Linear coordinates induced by the actual invertible two-copy map. -/
noncomputable def movingCoordinates (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (model : MovingCopies source 2) :
    letI := geometry.U_elementary hb (alpha R) rfl
    Additive (U R (alpha R)) ≃ₗ[ZMod 2] (Fin 2 → Fin 3 → ZMod 2) := by
  let := geometry.U_elementary hb (alpha R) rfl
  exact LinearEquiv.ofBijective (model.equiv.toMonoidHom.toAdditiveLeft.toZModLinearMap 2)
    model.equiv.bijective

theorem movingCoordinates_equivariant (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (model : MovingCopies source 2) :
    letI := geometry.U_elementary hb (alpha R) rfl
    ∀ (g : SL) (v : Additive (U R (alpha R))),
      movingCoordinates source geometry hb model (Offenders.linearize (uAction source) g v) =
        AbelianCore.DoubleCopy.natural (model.marking g) (movingCoordinates source geometry hb model v) := by
  let := geometry.U_elementary hb (alpha R) rfl
  intro g v
  obtain ⟨m, rfl⟩ := source.projection_surjective g
  funext i
  exact model.action m v.toMul (uAction source (source.projection m) v.toMul)
    (layerAction_apply source _ _ _ m v.toMul) i

/-- Both natural summands use the original model marking on the same image. -/
@[expose] noncomputable def markedImage (source : LocalSource L R) (model : MovingCopies source 2)
    (E : Subgroup (FreeAmalgam R)) : Subgroup SL :=
  (baseImage source E).map model.marking.toMonoidHom

theorem markedImage_card (source : LocalSource L R) (model : MovingCopies source 2)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ stabilizer R (alpha R)) :
    Nat.card (markedImage source model E) = (Q R (alpha R)).relIndex E := by
  exact (Nat.card_congr (model.marking.subgroupMap (baseImage source E)).toEquiv).symm.trans
    (baseImage_card source E hE)

/-- The actual two-copy action, with its given marking, preserves fixed codimension. -/
theorem markedImage_fixedCodim (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (model : MovingCopies source 2) (E : Subgroup (FreeAmalgam R)) :
    letI := geometry.U_elementary hb (alpha R) rfl
    fixedCodim AbelianCore.DoubleCopy.natural (markedImage source model E) =
      fixedCodim (Offenders.linearize (uAction source)) (baseImage source E) := by
  let := geometry.U_elementary hb (alpha R) rfl
  let := finite_Z R (alpha R)
  let : Finite (U R (alpha R)) :=
    Finite.of_injective (inclusion (U_le_Z (R := R) (alpha R))) (inclusion_injective _)
  exact (fixedCodim_map_equivariant (Offenders.linearize (uAction source))
    AbelianCore.DoubleCopy.natural model.marking.toMonoidHom
    (movingCoordinates source geometry hb model)
    (movingCoordinates_equivariant source geometry hb model) (baseImage source E)).symm

/-- Actual critical data for the finite doubled-natural calculation: an
order-four elementary image and fixed codimension at most two. -/
theorem critical_markedImage_data (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source) (model : MovingCopies source 2)
    (a : Vertex R) (hc : CriticalPair R (alpha R) a (geometry.exists_critical (alpha R) rfl)) :
    Nat.card (markedImage source model (X R a)) = 4 ∧
      IsElementaryAbelian 2 (markedImage source model (X R a)) ∧
      fixedCodim AbelianCore.DoubleCopy.natural (markedImage source model (X R a)) ≤ 2 := by
  let := X_elementary R a
  let := X_elementary R (alpha R)
  let := geometry.U_elementary hb (alpha R) rfl
  have ha := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := source.critical_reverse geometry (alpha R) rfl a ha hc
  have hAS := critical_X_le_stabilizer source geometry hb a ha (alpha R) hrev
  refine ⟨?_, ?_, ?_⟩
  · rw [markedImage_card source model (X R a) hAS,
      ← critical_displacement_eq_index source geometry hb a ha (alpha R) hrev]
    exact critical_displacement_eq_four source geometry hb hmodel a ha (alpha R) hrev
  · let := IsElementaryAbelian.subgroupOf (p := 2) hAS
    let : IsElementaryAbelian 2 (baseImage source (X R a)) :=
      IsElementaryAbelian.map (baseProjection source)
    exact IsElementaryAbelian.map model.marking.toMonoidHom
  · rw [markedImage_fixedCodim source geometry hb model]
    apply (Models.uAction_fixedCodim_le_xAction source geometry hb (baseImage source (X R a))).trans
    have hd := baseImage_fixedCodim source (X R a) hAS
    rw [critical_displacement_eq_four source geometry hb hmodel (alpha R) rfl a hc] at hd
    have htwo : fixedCodim (Offenders.linearize (xAction source)) (baseImage source (X R a)) = 2 :=
      (Nat.pow_right_injective (by decide : 1 < 2)) hd
    exact htwo.le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split
