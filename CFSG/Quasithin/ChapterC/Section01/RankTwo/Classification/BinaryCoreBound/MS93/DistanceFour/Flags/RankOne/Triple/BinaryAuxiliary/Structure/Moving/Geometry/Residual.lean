module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Escape.FixedPreimage.FirstIntersection.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing

/-!
# Genuine residual movement on the auxiliary quotient

Suppose the tilded residual fixes Y_delta/U_delta. Write H = V_beta,
K = Q_delta, A = Q_beta and U = U_delta at the selected incident flag.
The first core A normalizes H and U, while the contrary residual bound
makes H joined with U invariant under the residual. The incident supplement
A joined with the residual is the full actor P, so P normalizes H joined U.

The subgroup of K centralizing H joined U modulo Z_alpha is P-normalized
and contains K intersect A: use [H,A] <= Z_alpha and [U,K] <= Z_alpha.
The genuine incident-core intersection normally generates K inside P.
Consequently [H,K] <= Z_alpha, contradicting the source nonzero triple.
Conjugation carries this obstruction to every flag with the same residual
and second-layer denominator.

The normal-generation input is the matrix/parabolic calculation in
`FirstIntersection.Generation`. The argument needs only the earlier local
bounds and the selected nonzero triple; the natural-section and distance-four
inputs remain in the requested public contract.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.8), printed p.907, first paragraph, using claim (3) on p.906.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident
variable {G : Type*} [Group G]

private theorem commutator_join_le (A B K N : Subgroup G)
    (hAN : A ≤ normalizer N) (hBN : B ≤ normalizer N)
    (hA : ⁅A, K⁆ ≤ N) (hB : ⁅B, K⁆ ≤ N) : ⁅A ⊔ B, K⁆ ≤ N := by
  have h : A ⊔ B ≤ commutatorPreimage (A ⊔ B) K N :=
    sup_le (le_commutatorPreimage le_sup_left hA)
      (le_commutatorPreimage le_sup_right hB)
  exact (commutator_mono h le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (sup_le hAN hBN))

private theorem intersection_centralizes (P K A H U Z : Subgroup G)
    (hgen : ∀ N : Subgroup G, P ≤ normalizer N → K ⊓ A ≤ N → K ≤ N)
    (hKP : K ≤ P) (hPK : P ≤ normalizer K) (hPZ : P ≤ normalizer Z)
    (hHP : H ≤ P) (hUP : U ≤ P) (hPB : P ≤ normalizer (H ⊔ U : Subgroup _))
    (hUK : ⁅U, K⁆ ≤ Z) (hHA : ⁅H, A⁆ ≤ Z) : ⁅H, K⁆ ≤ Z := by
  let B := H ⊔ U
  let C := commutatorPreimage K B Z
  have hPC : P ≤ normalizer C :=
    commutatorPreimage_normalized K B Z P (hKP.trans hPZ) hPK hPB hPZ
  have hseed : K ⊓ A ≤ C := by
    apply le_commutatorPreimage inf_le_left
    rw [commutator_comm]
    exact commutator_join_le H U (K ⊓ A) Z (hHP.trans hPZ) (hUP.trans hPZ)
      ((commutator_mono le_rfl inf_le_right).trans hHA)
      ((commutator_mono le_rfl inf_le_left).trans hUK)
  have hKC : K ≤ C := hgen C hPC hseed
  rw [commutator_comm]
  exact (commutator_mono hKC le_sup_left).trans
    (commutator_commutatorPreimage_le K B Z (hKP.trans hPZ))

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Trivial residual action on Y/U would make the opposite core centralize
its first incident layer modulo the original Z_alpha. -/
theorem incident_first_core_le_Z_of_residual_le_second
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d)
    (hres : ⁅Y source i d, localFlagResidual source (!i) d⁆ ≤ secondFlagLayer source i d) :
    ⁅V R (beta R), localFlagKernel source (!i) d⁆ ≤ Z R (alpha R) := by
  let P := localFlagActor source (!i) d
  let K := localFlagKernel source (!i) d
  let A := flagKernel source i
  let H := V R (beta R)
  let U := secondFlagLayer source i d
  let T := localFlagResidual source (!i) d
  have hHY : H ≤ Y source i d := by
    simpa only [firstFlagLayer, localConjugate_one] using first_le_Y source i 1 d hd
  have hYP := Y_le_actor source geometry common.large_distance i d
  have hHP : H ≤ P := hHY.trans hYP
  have hUP : U ≤ P := (second_le_Y source i d).trans hYP
  have hAP : A ≤ P := flagKernel_le_incidentActor source i d hd
  have hPU : P ≤ normalizer U :=
    secondFlagLayer_normalized source geometry common.large_distance i d
  have hAH : A ≤ normalizer H := (flagKernel_le source i).trans
    (flagParabolic_normalizes_edgeRadius source geometry common.large_distance i hkernel)
  have hTP : T ≤ P := map_mono (flagResidual_le source (!i))
  have hUB : U ≤ normalizer (H ⊔ U : Subgroup _) := le_sup_right.trans (H ⊔ U).le_normalizer
  have hHB : H ≤ normalizer (H ⊔ U : Subgroup _) := le_sup_left.trans (H ⊔ U).le_normalizer
  have hTB : T ≤ normalizer (H ⊔ U : Subgroup _) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact commutator_join_le H U T (H ⊔ U) hHB hUB
      (((commutator_mono hHY le_rfl).trans hres).trans le_sup_right)
      ((le_normalizer_iff_commutator_le_left.mp (hTP.trans hPU)).trans le_sup_right)
  have hAB : A ≤ normalizer (H ⊔ U : Subgroup _) :=
    (le_inf hAH (hAP.trans hPU)).trans (normalizer_inf_normalizer_le_normalizer_sup H U)
  have hPB : P ≤ normalizer (H ⊔ U : Subgroup _) := by
    change localFlagActor source (!i) d ≤ _
    rw [← Incident.Pairing.flagKernel_sup_incidentResidual source i d hd]
    exact sup_le hAB hTB
  apply intersection_centralizes P K A H U (Z R (alpha R))
  · exact FirstIntersection.incident_core_le_of_intersection source i d hd
  · exact map_mono (flagKernel_le source (!i))
  · exact (map_mono (f := (MulAut.conj (embedM R d)).toMonoidHom)
      (flagKernel_normalized source (!i))).trans ((flagKernel source (!i)).le_normalizer_map _)
  · exact (localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _)
  · exact hHP
  · exact hUP
  · exact hPB
  · exact secondFlagLayer_commutator_le_Z source geometry common.large_distance i d
  · change ⁅V R (beta R), flagKernel source i⁆ ≤ _
    rw [hkernel]
    exact (edgeRadius_commutator_le_edgeZ geometry common.large_distance early).trans
      (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))

/-- The actual tilded residual moves the genuine auxiliary quotient at every
flag. The nonzero source triple and the incident-core geometry supply the
movement, with all local normality relative to the full actor. -/
theorem Y_residual_not_le_second
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (_hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (_natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) (d : M) :
    ¬ ⁅Y source i d, localFlagResidual source (!i) d⁆ ≤ secondFlagLayer source i d := by
  have hbase : ¬ ⁅Y source i p.delta2, localFlagResidual source (!i) p.delta2⁆ ≤
      secondFlagLayer source i p.delta2 := by
    intro h
    apply p.second_triple
    exact (commutator_mono
      (incident_first_core_le_Z_of_residual_le_second source geometry common early i hkernel
        p.delta2 p.delta2_neighbor h) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((show localFlagResidual source (!i) p.delta2 ≤ localFlagActor source (!i) p.delta2 from
          map_mono (flagResidual_le source (!i))).trans
            ((localFlagActor_le_stabilizer source (!i) p.delta2).trans (Z_normalized R _))))
  intro h
  apply hbase
  let a := p.delta2 * d⁻¹
  have ha : a * d = p.delta2 := by simp only [a, mul_assoc, inv_mul_cancel, mul_one]
  have hh := map_mono (f := (MulAut.conj (embedM R a)).toMonoidHom) h
  rw [map_commutator] at hh
  change ⁅localConjugate (Y source i d) a,
    localConjugate (localConjugate (flagResidual source (!i)) d) a⁆ ≤
      localConjugate (secondFlagLayer source i d) a at hh
  have ht := hh.trans (secondFlagLayer_conjugate_le source geometry common.large_distance i a d)
  simpa only [Y_conjugate, ← localConjugate_mul, ha, localFlagResidual] using ht

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
