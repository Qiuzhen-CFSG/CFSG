module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallIndexSource
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.ReducedSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableCriticalAlternatives
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableS3DistanceOne

/-!
# The original quintic pair in the reduced DGS critical configuration

The original Sylow lies in both full endpoints.  Their Borels are that same
Sylow, so the DGS reduction preserves both endpoints and their full cores.
The small-solvable/S₃ critical alternatives then give distance three with
commuting critical centers and nonzero displacement.  This distance is the
two-orbit DGS distance of the actual reduced F.1.1 graph; it is not the F.9
parameter of the reciprocal module construction.

Both D₁₀ and Sz(2) quotient branches are retained.  No core order bound or
Tits/full-Ree exclusion is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
include hG hempty hM hu hmany hcard e

/-- The whole original pair survives DGS reduction, including its overlap,
full embedded two-cores, edge stabilizer, and original ambient Sylow. -/
theorem source_quintic_dgs_reduced_pair
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let L : Fin 2 → Subgroup G := ![H,X]
    let J := Reduction.G₀ L (T : Subgroup G)
    let F := Reduction.reducedFamily L (T : Subgroup G)
    HypothesisF11 L (T : Subgroup G) ∧
      H ⊓ X = T ∧
      SuzukiContainment.reducedSylow L (T : Subgroup G) = T ∧
      Reduction.B₀ L (T : Subgroup G) = T ∧
      (∀ i, Reduction.P₀ L (T : Subgroup G) i = L i) ∧
      J = H ⊔ X ∧
      (∀ i, (F i).map J.subtype = family L i ∧
        (Q F (base F i)).map J.subtype = (family L i).pCoreIn 2) ∧
      (MulAction.stabilizer J ({base F false,base F true} : Set (Vertex F))).map
        J.subtype = T ∧
      ∃ S : Sylow 2 J, (S : Subgroup J).map J.subtype = T := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  obtain ⟨hF,hHX,hNH,hNX,_⟩ := Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
    hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)
  have hLi (i : Fin 2) : (T : Subgroup G) ≤ L i := by
    fin_cases i
    · exact hH.1.1.2
    · exact le_sup_right
  have hB (i : Fin 2) : borel (L i) (T : Subgroup G) = T := by
    change L i ⊓ normalizer ((T : Subgroup G) ⊓ L i : Subgroup G) = T
    rw [inf_eq_left.mpr (hLi i)]
    fin_cases i
    · exact hNH
    · exact hNX
  have hP (i : Fin 2) : parabolic L (T : Subgroup G) i = L i := by
    change L i ⊔ (T : Subgroup G) ⊔ borel (L (other i)) _ = L i
    rw [hB,sup_eq_left.mpr (hLi i),sup_eq_left.mpr (hLi i)]
  have hS := hF.quintic_reducedSylow_eq hH.1.1.2
  have hB₀ : Reduction.B₀ L (T : Subgroup G) = T := by
    rw [Reduction.B₀_eq_source hF,hS,commonBorel,hB,hB,sup_idem,sup_idem]
  have hP₀ (i : Fin 2) : Reduction.P₀ L (T : Subgroup G) i = L i := by
    rw [Reduction.P₀_eq_source hF,hS,hP]
  have hJ : J = H ⊔ X := by
    change Reduction.P₀ L (T : Subgroup G) 0 ⊔ Reduction.P₀ L (T : Subgroup G) 1 = _
    rw [hP₀,hP₀]
    rfl
  have hLJ (i : Fin 2) : L i ≤ J := by
    rw [hJ]
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hTJ : (T : Subgroup G) ≤ J := (hLi 0).trans (hLJ 0)
  have hmap (i : Bool) : (F i).map J.subtype = family L i := by
    cases i
    · change ((Reduction.P₀ L (T : Subgroup G) 0).subgroupOf J).map J.subtype = L 0
      rw [hP₀,map_subgroupOf_eq_of_le (hLJ 0)]
    · change ((Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J).map J.subtype = L 1
      rw [hP₀,map_subgroupOf_eq_of_le (hLJ 1)]
  refine ⟨hF,hHX,hS,hB₀,hP₀,hJ,?_,?_,?_⟩
  · intro i
    refine ⟨hmap i,?_⟩
    rw [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base,
      ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _ J.subtype_injective,hmap]
  · rw [(Reduction.reduced_graph_setup hF).2.2.2.1,hB₀,
      map_subgroupOf_eq_of_le hTJ]
  · exact ⟨T.subtype hTJ,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ]⟩

/-- The actual reduced F.1.1 graph has DGS critical distance three and a
critical predecessor triple with nonzero commuting displacement. -/
theorem source_quintic_dgs_critical_three
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
    b F = 3 ∧
      ∃ a beta a' : Vertex F,
        IsCriticalPair F a a' ∧ (graph F).Adj a beta ∧
        (graph F).dist beta a' + 1 = b F ∧
        ⁅Z F a,Z F a'⁆ = ⊥ ∧ ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let F := Reduction.reducedFamily L (T : Subgroup G)
  have hF := (source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi).1
  have hm := Section02.SolvableAmalgam.source_index_five_models
    hG T hempty hM hu hmany hcard e H hH.1 hi
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hsize (i : Fin 2) : Nat.card (L i ⧸ pCore 2 (L i)) < 72 := by
    fin_cases i
    · change Nat.card (H ⧸ pCore 2 H) < 72
      rcases hm with hd | hs
      · rw [Nat.card_congr hd.some.toEquiv,DihedralGroup.nat_card]
        norm_num
      · rw [Nat.card_congr hs.some.toEquiv,BenderSuzuki.MatrixGroups.suzukiZero_card]
        norm_num
    · change Nat.card (X ⧸ pCore 2 X) < 72
      rw [Nat.card_congr eX.toEquiv,Nat.card_perm,Nat.card_fin]
      norm_num
  have ht := Reduction.reduced_triple hF
  obtain ⟨a,a',hc⟩ := Reduction.reduced_criticalPair hF
  have hne : a' ≠ a := by
    intro he
    have hd := hc.1
    rw [he,SimpleGraph.dist_self] at hd
    exact (Nat.ne_of_gt (source_b_positive ht)) hd.symm
  obtain ⟨beta,hab,hd⟩ := exists_predecessor F ht.generate a' a hne
  rw [SimpleGraph.dist_comm (u := a') (v := beta),
    SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hd
  obtain ⟨hcomm,hcases⟩ := Assembly.reduced_small_solvable_critical_alternatives
    hF false hm hsize hc hab hd
  rcases hcases with hb | ⟨hb,hdisp⟩
  · exact (Assembly.small_solvable_s3_distance_one_exclusion hF hm ⟨eX⟩ hb).elim
  · exact ⟨hb,a,beta,a',hc,hab,hd,hcomm,hdisp⟩

end CFSG.Quasithin.Chapter14.Section06
