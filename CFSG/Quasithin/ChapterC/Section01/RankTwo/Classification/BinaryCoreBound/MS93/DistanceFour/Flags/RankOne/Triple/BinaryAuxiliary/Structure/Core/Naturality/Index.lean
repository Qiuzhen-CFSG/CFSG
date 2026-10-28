module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Index.Pairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Index.FixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Escape.FixedPreimage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Pencils

/-!
# The source bound on the literal binary auxiliary core

For the selected second flag, let P be its full parabolic, K its core,
U the second layer, D the fixed preimage in Y/U, and X = [D,K] Z_alpha.
The source endpoint supplies an element of P that fixes V_beta modulo U
and acts nontrivially on the supplied natural moving factor. The already
proved incident-core intersection D ∩ V_beta ≤ U and generation
Y = V_beta [Y,P] bound |D/U| by two. The commutator pairing then bounds
|X/Z_alpha| by |K/Q_alpha| = 4, transported through the original projection.

Only the generation theorem is used from `Escape.FixedPreimage`; no endpoint
bound from the p.908 escape, auxiliary naturality, cross-commutator conclusion,
or action descent on the whole Y/U is assumed. The first natural section
keeps its residual-fixed denominator, and every quotient is relative to
its stated local subgroup.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed pp.905--907, the assertion that X/Z_alpha is a
natural SL₂(2)-module on p.907. This module proves its upper size bound;
nonzero residual action and naturality are assembled by the parent module.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem local_core_index (source : LocalSource L R) (j : Bool) (d : M) :
    (Q R (alpha R)).relIndex (localFlagKernel source j d) = 4 := by
  rw [Pencils.localFlagKernel_eq_matrix_preimage, Q_alpha R source.two_group source.core_le,
    relIndex_map_map_of_injective _ _ (embedM_injective R), ← source.projection_kernel,
    relIndex_ker, map_comap_eq_self_of_surjective source.projection_surjective]
  unfold Pencils.matrixCore
  rw [Nat.card_congr (((modelParabolic source.flag j).pCoreIn 2).equivMapOfInjective
    (MulAut.conj (source.projection d)).toMonoidHom
    (MulAut.conj (source.projection d)).injective).toEquiv.symm]
  rw [pCoreIn, Nat.card_congr ((pCore 2 (modelParabolic source.flag j)).equivMapOfInjective
    (modelParabolic source.flag j).subtype
    (modelParabolic source.flag j).subtype_injective).toEquiv.symm]
  exact (Matrix.PSL3Two.ParabolicCoreModel.core_data
    (modelParabolicEquivSymmetric source.flag j)).2

/-- The source endpoint fixes the first layer modulo U and acts nontrivially
on the moving natural plane. Its fixed line bounds the literal D/U. -/
theorem fixed_preimage_index_le_two
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) :
    (secondFlagLayer source i p.delta0).relIndex (D source i p.delta0) ≤ 2 := by
  let c : FlagCriticalData source geometry i := {
    middle := p.middle, endpoint := p.endpoint, critical := p.critical,
    middle_neighbor := p.middle_neighbor, first_distance := p.first_distance,
    second_distance := p.second_distance, middle_triple := p.middle_triple }
  let Y₀ := Y source i p.delta0
  let P := localFlagActor source (!i) p.delta0
  let U₀ := secondFlagLayer source i p.delta0
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite Y₀ := Finite.of_injective (inclusion
    ((Y_le_radius source i p.delta0).trans (geometry.V_local _ rfl common.large_distance)))
      (inclusion_injective _)
  have hEP : Z R p.endpoint ≤ P :=
    Incident.endpoint_le_incidentActor source geometry hb i hkernel c
      p.delta0 p.delta0_neighbor
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp p.endpoint_not_le
  let e : P := ⟨a,hEP ha⟩
  have he : moving.val.projection e ≠ 1 := by
    intro ht
    have hh := MonoidHom.mem_ker.mpr ht
    rw [moving.property] at hh
    exact han hh
  have hE : zpowers a ≤ Q R (beta R) :=
    (zpowers_le.mpr ha).trans (c.endpoint_le_edgeKernel hb)
  have hWE : ⁅V R (beta R), zpowers (e : FreeAmalgam R)⁆ ≤ U₀ :=
    (((commutator_mono le_rfl hE).trans
      (edgeRadius_commutator_le_edgeZ geometry common.large_distance early)).trans
        (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))).trans
          (Z_le_secondFlagLayer source i p.delta0)
  have hYY : ⁅Y₀,Y₀⁆ ≤ U₀ :=
    ((commutator_mono (Y_le_radius source i p.delta0)
      ((Y_le_radius source i p.delta0).trans (V_le_Q geometry common.large_distance _ rfl))).trans
        (early.commutator_le_Z _ rfl)).trans (Z_le_secondFlagLayer source i p.delta0)
  exact CoreIndex.fixed_index_le_two P Y₀ (V R (beta R)) U₀ moving.val
    (Y_le_actor source geometry common.large_distance i p.delta0)
    (second_le_Y source i p.delta0) (Y_normalized source i p.delta0)
    (Incident.secondFlagLayer_normalized source geometry common.large_distance i p.delta0)
    (Y_eq_first_sup_commutator source i natural p.delta0 p.delta0_neighbor) hYY
    (D_inf_first_le_second source geometry common early i hkernel p.delta0 p.delta0_neighbor)
    e he hWE

/-- The literal auxiliary core X = [D,K] Z_alpha has quotient order at most
four. All size and commutator-pairing premises are discharged from the
source configuration and the supplied moving natural factor. -/
theorem core_index_le_four
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) :
    (Z R (alpha R)).relIndex (X source i p.delta0) ≤ 4 := by
  let D₀ := D source i p.delta0
  let K := localFlagKernel source (!i) p.delta0
  let X₀ := X source i p.delta0
  have hD : D₀ ≤ V R (alpha R) :=
    (D_le_Y source i p.delta0).trans (Y_le_radius source i p.delta0)
  have hX : X₀ ≤ V R (alpha R) :=
    (X_le_D source geometry common.large_distance i p.delta0).trans hD
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite D₀ := Finite.of_injective
    (inclusion (hD.trans (geometry.V_local _ rfl common.large_distance))) (inclusion_injective _)
  let : Finite K := Finite.of_injective
    (inclusion (localFlagKernel_le_stabilizer source (!i) p.delta0)) (inclusion_injective _)
  let : Finite X₀ := Finite.of_injective
    (inclusion (hX.trans (geometry.V_local _ rfl common.large_distance))) (inclusion_injective _)
  let := CoreNaturality.denominator_normal source geometry common.large_distance i p.delta0
  let := CoreNaturality.quotient_elementary source geometry common early i p.delta0
  have hDQ : ⁅D₀, Q R (alpha R)⁆ ≤ Z R (alpha R) :=
    (commutator_mono hD le_rfl).trans (early.commutator_le_Z _ rfl)
  have hDX : ⁅D₀, X₀⁆ ≤ Z R (alpha R) :=
    (commutator_mono le_rfl (hX.trans (V_le_Q geometry common.large_distance _ rfl))).trans hDQ
  have hKX : ⁅K,X₀⁆ ≤ Z R (alpha R) := by
    rw [commutator_comm]
    exact CoreNaturality.X_kernel_commutator_le source geometry common.large_distance i p.delta0
  have hh := CoreIndex.index_le_of_fixed_index_le_two D₀ (secondFlagLayer source i p.delta0)
    K (Q R (alpha R)) X₀ (Z R (alpha R)) rfl
    (Incident.secondFlagLayer_commutator_le_Z source geometry common.large_distance i p.delta0)
    hDQ hDX hKX
    (fixed_preimage_index_le_two source geometry common hb early i hkernel natural p moving)
  exact hh.trans_eq (local_core_index source (!i) p.delta0)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
