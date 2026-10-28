module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Escape.FixedPreimage.FirstIntersection.Generation

/-!
# The first-layer intersection of the full-actor fixed preimage

Write P for the opposite full parabolic, K for its core, A for the first
core, W for V_beta, U for the second flag layer, and H = D intersect W.
The displacement bound [D,P] ≤ U makes H U invariant under P. Since
[U,K] ≤ Z_alpha, the subgroup of K centralizing H U modulo Z_alpha is
P-normalized and contains K intersect A, using [W,A] ≤ Z_alpha.
The incident-core normal-generation theorem therefore gives [H,K] ≤ Z_alpha.
The fixed preimage in W is the g = 1 summand in the definition of U.

This calculation uses neither an endpoint bound nor the later auxiliary
module structure. All normalization is relative to the actual local actors.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed pp.907--908, the deduction of D_delta = U_delta.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.FirstIntersection
variable {G : Type*} [Group G]

/-- Centralization of the incident intersection propagates along its normal
closure. Adjoining U makes H invariant, because [H,P] lies in U. -/
private theorem intersection_commutator_le (P K A D U W Z : Subgroup G)
    (hgen : ∀ N : Subgroup G, P ≤ normalizer N → K ⊓ A ≤ N → K ≤ N)
    (hKP : K ≤ P) (hDP : D ≤ P) (hUD : U ≤ D)
    (hPK : P ≤ normalizer K) (hPZ : P ≤ normalizer Z)
    (hcomm : ⁅D, P⁆ ≤ U) (hUK : ⁅U, K⁆ ≤ Z) (hWA : ⁅W, A⁆ ≤ Z) :
    ⁅D ⊓ W, K⁆ ≤ Z := by
  let H := D ⊓ W
  let B := H ⊔ U
  have hBD : B ≤ D := sup_le inf_le_left hUD
  have hBN : B ≤ normalizer Z := hBD.trans (hDP.trans hPZ)
  have hPB : P ≤ normalizer B := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hBD le_rfl).trans hcomm).trans le_sup_right
  let C := commutatorPreimage K B Z
  have hPC : P ≤ normalizer C :=
    commutatorPreimage_normalized K B Z P (hKP.trans hPZ) hPK hPB hPZ
  have hseed : K ⊓ A ≤ C := by
    apply le_commutatorPreimage inf_le_left
    rw [commutator_comm]
    have hB : B ≤ commutatorPreimage B (K ⊓ A) Z := by
      apply sup_le
      · exact le_commutatorPreimage le_sup_left
          ((commutator_mono inf_le_right inf_le_right).trans hWA)
      · exact le_commutatorPreimage le_sup_right
          ((commutator_mono le_rfl inf_le_left).trans hUK)
    exact (commutator_mono hB le_rfl).trans
      (commutator_commutatorPreimage_le B (K ⊓ A) Z hBN)
  have hKC : K ≤ C := hgen C hPC hseed
  rw [commutator_comm]
  exact (commutator_mono hKC le_sup_left).trans
    (commutator_commutatorPreimage_le K B Z (hKP.trans hPZ))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.FirstIntersection

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
/-- The part of the full-actor fixed preimage in the first incident layer
is already in the second layer, without any endpoint or escape premise. -/
theorem D_inf_first_le_second (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) :
    D source i d ⊓ V R (beta R) ≤ secondFlagLayer source i d := by
  let P := localFlagActor source (!i) d
  let K := localFlagKernel source (!i) d
  have hKP : K ≤ P := map_mono (flagKernel_le source (!i))
  have hPK : P ≤ normalizer K :=
    (map_mono (f := (MulAut.conj (embedM R d)).toMonoidHom)
      (flagKernel_normalized source (!i))).trans
        ((flagKernel source (!i)).le_normalizer_map _)
  have hc : ⁅D source i d ⊓ V R (beta R), K⁆ ≤ Z R (alpha R) := by
    apply FirstIntersection.intersection_commutator_le P K (flagKernel source i)
      (D source i d) (secondFlagLayer source i d) (V R (beta R)) (Z R (alpha R))
    · exact FirstIntersection.incident_core_le_of_intersection source i d hd
    · exact hKP
    · exact (D_le_Y source i d).trans
        (Y_le_actor source geometry common.large_distance i d)
    · exact second_le_D source geometry common.large_distance i d
    · exact hPK
    · exact (localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _)
    · exact D_commutator_actor source geometry common.large_distance i d
    · exact Incident.secondFlagLayer_commutator_le_Z source geometry common.large_distance i d
    · rw [hkernel]
      exact (edgeRadius_commutator_le_edgeZ geometry common.large_distance early).trans
        (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
  apply le_trans (le_commutatorPreimage (Q := V R (beta R)) inf_le_right hc)
  apply le_iSup_of_le (1 : M)
  apply le_iSup_of_le hd
  simp only [firstFlagLayer, localConjugate_one]
  exact le_rfl
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
