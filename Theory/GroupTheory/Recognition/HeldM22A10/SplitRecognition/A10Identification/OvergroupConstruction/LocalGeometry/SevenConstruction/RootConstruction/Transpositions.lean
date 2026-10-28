module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Factor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootActions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Transpositions.ActorConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Transpositions.ActorRelations
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Transpositions.PermutationCriterion
/-!
# Held's four marked transpositions

The actor constructed from the supplied A6 conjugates the four marks inside
the symmetric extension. Their commuting triple is fused with pi. Its ambient
centralizer has order 384, excluding the alternative in which the three marks
are triple swaps. The final theorem takes only the original local hypotheses
and the explicit corrected six-point data, root factor and S7 equivalence.
No actor, conjugacy, transposition or compatible marking remains assumed.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemmas 5.9–5.10, printed p.238.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
variable {G : Type*} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e) (F : RootFactor D e L)
  (a : RootTranspositionActor D e L F)
  (s : (F.W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7))
local notation "m₀" => rootMark D e L F 0
local notation "m₂" => rootMark D e L F 2
local notation "m₃" => rootMark D e L F 3
include a in
public theorem rootMark_isSwap (i : Fin 4) : (s (rootMark D e L F i)).IsSwap := by
  have hc := rootMark_commuting D e L F
  have hn := rootMark_distinct D e L F
  have hswap : (s m₀).IsSwap :=
    PermutationCriterion.isSwap_of_odd_commuting_triple (s m₀) (s m₂) (s m₃)
      (by rw [← map_pow, rootMark_square, map_one])
      (by rw [← map_pow, rootMark_square, map_one])
      (by rw [← map_pow, rootMark_square, map_one])
      (rootMark_zero_odd D e L F s)
      (hc.1.map s.toMonoidHom) (hc.2.1.map s.toMonoidHom) (hc.2.2.map s.toMonoidHom)
      (fun h => hn.1 (s.injective h)) (fun h => hn.2.1 (s.injective h))
      (fun h => hn.2.2 (s.injective h))
      (s.toMonoidHom.map_isConj (RootTranspositionActor.marked_conjugacy D e L F a 2))
      (s.toMonoidHom.map_isConj (RootTranspositionActor.marked_conjugacy D e L F a 3))
      (by simpa only [map_mul] using RootTranspositionActor.triple_centralizer_not_five D e L F a s)
  have hconj := s.toMonoidHom.map_isConj (RootTranspositionActor.marked_conjugacy D e L F a i)
  apply Perm.isSwap_iff_cycleType.mpr
  exact (Perm.isConj_iff_cycleType_eq.mp hconj).symm.trans (Perm.isSwap_iff_cycleType.mp hswap)

include a in
public theorem marked_transpositions_of_actor :
    ∀ x : (F.W ⊔ zpowers (mu' D e) : Subgroup G),
      (x : G) ∈ ({mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e} : Set G) →
      (s x).IsSwap := by
  intro x hx
  rcases hx with hx | hx | hx | hx
  · have he : x = rootMark D e L F 0 := Subtype.ext hx
    rw [he]
    exact rootMark_isSwap D e L F a s 0
  · have he : x = rootMark D e L F 1 := Subtype.ext hx
    rw [he]
    exact rootMark_isSwap D e L F a s 1
  · have he : x = rootMark D e L F 2 := Subtype.ext hx
    rw [he]
    exact rootMark_isSwap D e L F a s 2
  · have he : x = rootMark D e L F 3 := Subtype.ext hx
    rw [he]
    exact rootMark_isSwap D e L F a s 3
/-- Held 5.10 for the explicitly supplied root factor and symmetric equivalence.
The source actor and its extra conjugation relations are discharged here. -/
public theorem marked_transpositions [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (_hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    ∀ x : (F.W ⊔ zpowers (mu' D e) : Subgroup G),
      (x : G) ∈ ({mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e} : Set G) →
      (s x).IsSwap := by
  obtain ⟨actor⟩ := exists_rootTranspositionActor D e L F hfusion
  exact marked_transpositions_of_actor D e L F actor s

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
