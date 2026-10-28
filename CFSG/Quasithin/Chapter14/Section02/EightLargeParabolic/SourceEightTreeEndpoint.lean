module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightCentralBall
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightHalfActor

/-!
# The full original eight endpoint on the universal tree

The reduced eight endpoint contains its starred group, which is the full
original H, and lies in the original parabolic H. Thus both the full
stabilizer and its intrinsic local actor are the same original subgroup.
The tree-cover equivalence retains every ambient group element pointwise.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeEndpoint
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S H : Subgroup G}

/-- The original full endpoint and its intrinsic actor have the same literal marking. -/
@[expose] def HasEightTreeEndpoint (h : HypothesisF11 L S) (H : Subgroup G) : Prop :=
    (∃ j : RankTwo.stabilizer (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) true) ≃* H,
      ∀ x, (j x:G)=((G₀ L S).subtype.comp (bOne_tree_map h)) x) ∧
    graphLocalGroup (reducedFamily L S) (RankTwo.base (reducedFamily L S) true)=
      RankTwo.stabilizer (reducedFamily L S) (RankTwo.base (reducedFamily L S) true)

private theorem base_endpoint_equiv (h : HypothesisF11 L S)
    (hP : P₀ L S 1=H) :
    ∃ j : RankTwo.stabilizer (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) true) ≃* H,
      ∀ x, (j x:G)=((G₀ L S).subtype.comp (bOne_tree_map h)) x := by
  let cov := bOne_tree_cover h
  have hb : RankTwo.stabilizer (reducedFamily L S)
      (cov.vertex (base (Universal.cosetFamily (reducedAmalgam L S)) true))=
        (P₀ L S 1).subgroupOf (G₀ L S) := by
    rw [cov.vertex_base]
    change MulAction.stabilizer (G₀ L S) (base (reducedFamily L S) true)=_
    rw [stabilizer_base]
    rfl
  let j := (cov.stabilizerEquiv _).trans ((MulEquiv.subgroupCongr hb).trans
    ((subgroupOfEquivOfLe (show P₀ L S 1≤G₀ L S from le_sup_right)).trans
      (MulEquiv.subgroupCongr hP)))
  exact ⟨j,fun _ => rfl⟩

private theorem actor_eq_endpoint (h : HypothesisF11 L S)
    (eK : (family L true ⧸ pCore 2 (family L true)) ≃* Theory.PSL2.BinaryGroup 3)
    (hs : starredParabolic L S 1=H) (hp : P₀ L S 1=H) :
    graphLocalGroup (reducedFamily L S) (RankTwo.base (reducedFamily L S) true)=
      RankTwo.stabilizer (reducedFamily L S) (RankTwo.base (reducedFamily L S) true) := by
  apply map_injective (G₀ L S).subtype_injective
  rw [reduced_graphLocalGroup_image h]
  change family (enlargedEndpoint L S) true=(MulAction.stabilizer (G₀ L S)
    (base (reducedFamily L S) true)).map (G₀ L S).subtype
  rw [stabilizer_base]
  change enlargedEndpoint L S 1=((P₀ L S 1).subgroupOf (G₀ L S)).map (G₀ L S).subtype
  rw [map_subgroupOf_eq_of_le (show P₀ L S 1≤G₀ L S from le_sup_right),
    reduced_enlargedEndpoint_eq_starred_of_linear h 1 eK,hs,hp]

private theorem endpoint_eq (h : HypothesisF11 L S)
    (hs : starredParabolic L S 1=H) (hp : parabolic L S 1=H) : P₀ L S 1=H := by
  apply le_antisymm ((P₀_le h 1).trans_eq hp)
  rw [←hs]
  exact le_sup_left

private theorem reversed_starred :
    starredParabolic ![L 1,L 0] S 1=starredParabolic L S 0 := rfl
private theorem reversed_parabolic :
    parabolic ![L 1,L 0] S 1=parabolic L S 0 := rfl

private theorem reversed_endpoint_eq {K U : Subgroup G} (h : HypothesisF11 ![K,U] S)
    (hs : starredParabolic ![K,U] S 0=H) (hp : parabolic ![K,U] S 0=H) :
    P₀ ![U,K] S 1=H :=
  endpoint_eq (L := ![U,K]) (S := S) (H := H) h.swap
    ((reversed_starred (L := ![K,U]) (S := S)).trans hs)
    ((reversed_parabolic (L := ![K,U]) (S := S)).trans hp)

private theorem assemble {K U : Subgroup G} (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (hs : starredParabolic ![K,U] S 0=H) (hp : parabolic ![K,U] S 0=H) :
    HasEightTreeEndpoint h.swap H := by
  have hP := reversed_endpoint_eq (K := K) (U := U) (S := S) h hs hp
  exact ⟨base_endpoint_equiv (L := ![U,K]) (S := S) h.swap hP,
    actor_eq_endpoint (L := ![U,K]) (S := S) h.swap eK
      ((reversed_starred (L := ![K,U]) (S := S)).trans hs) hP⟩

end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ

set_option maxHeartbeats 800000 in
/-- The full reduced eight endpoint is the original H. -/
theorem source_eight_reduced_endpoint : P₀ Lₛ Sₛ 1=H := by
  exact reversed_endpoint_eq
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
    (source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).1
    (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1

set_option maxHeartbeats 800000 in
/-- The original tree stabilizer has the literal pointwise marking onto H;
its reduced local actor is the whole reduced endpoint stabilizer. -/
theorem source_eight_tree_endpoint :
    HasEightTreeEndpoint
      (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) H := by
  exact assemble
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
    (residualQuotientEquiv H eR)
    (source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).1
    (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeEndpoint
