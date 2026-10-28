module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Layers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Action.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData
public import Theory.GroupTheory.Commutator.ElementaryQuotientIndexTwoQuadratic

/-!
# The core action on the auxiliary quotient and the transported nonzero triple

An incident opposite core has reflection image in the genuine S3 quotient
of the first parabolic. Its intersection with the first core therefore has
index two. The elementary quotient of the first layer makes this action
quadratic. Transporting to every incident first layer and taking their span
proves [Y_delta,Q_delta] <= U_delta, so the full core fixes Y_delta/U_delta.

The original nonzero triple from p.906 also transports to every second flag,
with its tilded residual unchanged. In particular Y_delta is strictly larger
than U_delta. This does not identify the action of the residual on Y_delta/U_delta;
that is a separate obligation from the nonzero triple on Y_delta/Z_alpha.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.8), printed pp.906--907. All normality and quotients are relative
to the actual finite layers, not the ambient free amalgam.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident Incident.Pairing Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem incident_core_index (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (flagKernel source i).relIndex (localFlagKernel source (!i) d) = 2 := by
  obtain ⟨π, hπ, hk⟩ := exists_barProjection source i
  obtain ⟨t, ht, htn, himage⟩ := exists_incident_reflection source i d hd π hπ hk
  rw [← relIndex_subgroupOf (incidentKernel_le_flagParabolic source i d hd), ← hk,
    relIndex_ker]
  apply Nat.card_eq_two_iff.mpr
  refine ⟨⟨1, (himage 1).mpr (Or.inl rfl)⟩, ⟨t, (himage t).mpr (Or.inr rfl)⟩, ?_, ?_⟩
  · intro he
    exact htn (congrArg Subtype.val he).symm
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (himage x).mp x.property with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)

/-- The opposite incident core acts quadratically on the original barred edge layer. -/
theorem incident_first_quadratic (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) :
    ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆, localFlagKernel source (!i) d⁆ ≤
      Z R (alpha R) := by
  let H := V R (beta R)
  let N := Z R (alpha R)
  let K := localFlagKernel source (!i) d
  let B := flagKernel source i ⊓ K
  let : IsElementaryAbelian 2 H :=
    edgeRadius_elementary geometry common.large_distance (alpha R) (beta R) rfl (base_adjacent R)
  let : (N.subgroupOf H).Normal := inferInstance
  apply commutator_commutator_le_of_elementary_quotient_index_two H N B K
    Z_le_edgeRadius
    ((incidentKernel_le_flagParabolic source i d hd).trans
      (flagParabolic_normalizes_edgeRadius source geometry common.large_distance i hkernel))
    ((localFlagKernel_le_stabilizer source (!i) d).trans (Z_normalized R _))
    inferInstance (IsElementaryAbelian.quotient _) inf_le_right
  · change (flagKernel source i ⊓ K).relIndex K = 2
    rw [inf_relIndex_right]
    exact incident_core_index source i d hd
  · exact (commutator_mono le_rfl inf_le_left).trans (by
      rw [hkernel]
      exact (edgeRadius_commutator_le_edgeZ geometry common.large_distance early).trans
        (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)))
private theorem first_core_le_fixed (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (g d : M) (hd : flagIncident source i g d) :
    ⁅firstFlagLayer (R := R) g, localFlagKernel source (!i) d⁆ ≤
      commutatorPreimage (firstFlagLayer (R := R) g)
        (localFlagKernel source (!i) d) (Z R (alpha R)) := by
  have hi : flagIncident source i 1 (g⁻¹ * d) := by
    simpa only [inv_mul_cancel] using
      (flagIncident_left source i g⁻¹ g d).mpr hd
  have hn := (incidentKernel_le_flagParabolic source i (g⁻¹ * d) hi).trans
    (flagParabolic_normalizes_edgeRadius source geometry common.large_distance i hkernel)
  have hc := map_mono (f := (MulAut.conj (embedM R g)).toMonoidHom)
    (le_normalizer_iff_commutator_le_left.mp hn)
  have hq := map_mono (f := (MulAut.conj (embedM R g)).toMonoidHom)
    (incident_first_quadratic source geometry common early i hkernel (g⁻¹ * d) hi)
  have he : (localFlagKernel source (!i) (g⁻¹ * d)).map
      (MulAut.conj (embedM R g)).toMonoidHom = localFlagKernel source (!i) d := by
    change localConjugate (localConjugate (flagKernel source (!i)) (g⁻¹ * d)) g = _
    rw [← localConjugate_mul, mul_inv_cancel_left]
    rfl
  rw [map_commutator, he] at hc
  rw [map_commutator, map_commutator, he] at hq
  exact le_commutatorPreimage hc (hq.trans_eq (localConjugate_Z g))

/-- The actual two-core fixes the quotient Y_delta/U_delta at every flag. -/
theorem Y_core_le_second (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (d : M) :
    ⁅Y source i d, localFlagKernel source (!i) d⁆ ≤ secondFlagLayer source i d := by
  have hh : Y source i d ≤ commutatorPreimage (Y source i d)
      (localFlagKernel source (!i) d) (secondFlagLayer source i d) := by
    apply iSup_le
    intro g
    apply iSup_le
    intro hg
    exact le_commutatorPreimage (first_le_Y source i g d hg)
      ((first_core_le_fixed source geometry common early i hkernel g d hg).trans
        (le_iSup_of_le g (le_iSup_of_le hg le_rfl)))
  exact (commutator_mono hh le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      (Y_normalizes_second source geometry common.large_distance i d))
omit [Finite M] in
/-- Transport the nonzero source triple, retaining its actual tilded residual. -/
theorem Y_core_residual_triple_not_le (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) (p : SourceFlagPreparatoryData source geometry i) (d : M) :
    ¬ ⁅⁅Y source i d, localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) := by
  have hbase : ¬ ⁅⁅Y source i p.delta2, localFlagKernel source (!i) p.delta2⁆,
      localFlagResidual source (!i) p.delta2⁆ ≤ Z R (alpha R) := by
    intro h
    apply p.second_triple
    have hf : V R (beta R) ≤ Y source i p.delta2 := by
      simpa only [firstFlagLayer, localConjugate_one] using
        first_le_Y source i 1 p.delta2 p.delta2_neighbor
    exact (commutator_mono (commutator_mono hf le_rfl) le_rfl).trans h
  intro h
  apply hbase
  let a := p.delta2 * d⁻¹
  have ha : a * d = p.delta2 := by simp only [a, mul_assoc, inv_mul_cancel, mul_one]
  have hh := map_mono (f := (MulAut.conj (embedM R a)).toMonoidHom) h
  rw [map_commutator, map_commutator] at hh
  change ⁅⁅localConjugate (Y source i d) a,
    localConjugate (localConjugate (flagKernel source (!i)) d) a⁆,
    localConjugate (localConjugate (flagResidual source (!i)) d) a⁆ ≤
      localConjugate (Z R (alpha R)) a at hh
  simpa only [Y_conjugate, ← localConjugate_mul, localConjugate_Z, ha,
    localFlagKernel, localFlagResidual] using hh

omit [Finite M] in
/-- The nonzero source triple forces the auxiliary quotient to be nontrivial. -/
theorem Y_not_le_second (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (d : M) :
    ¬ Y source i d ≤ secondFlagLayer source i d := by
  intro h
  apply Y_core_residual_triple_not_le source geometry i p d
  exact (commutator_mono ((commutator_mono h le_rfl).trans
    (secondFlagLayer_commutator_le_Z source geometry hlarge i d)) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((show localFlagResidual source (!i) d ≤ localFlagActor source (!i) d from
        map_mono (flagResidual_le source (!i))).trans
        ((localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _))))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
