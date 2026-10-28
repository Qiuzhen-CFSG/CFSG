module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightCorrectedGeometry
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfActorFaithful
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceApartmentReflections
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathTorus
public import Theory.GroupTheory.WeakBNPair.RegularTree.FaithfulPathExchange

/-!
# Faithful marked actors on the original mixed-field apartment

The actual fields and endpoint quotient marks provide simultaneous opposite
root coordinates. The full Cartan diagonal comes from its actual local actor
intersection. Faithfulness kills the correction kernel in the rank-one braid,
and the original reversing reflection gives literal half-path exchange.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceApartmentExchange
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S

private theorem faithful_exchange_of_reflections (h:HypothesisF11 L S)
    (c:CompatibleCartans L (reducedSylow L S)) (d:SixPathSmallActorGeometry c)
    (hq:SourceHalfPathQuotients.HasCanonicalHalfPathQuotients h c)
    (hval:∀ v:SourceVertex A,Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (hzero:SourceHalfActorFaithful.HasFaithfulHalfActors c)
    (href:∀ {a b:SourceVertex A} (p:(sourceGraph A).Walk a b),p.IsPath → p.length=12 →
      (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) →
      ∃ x∈halfPathActor (X := (A).Universal) p 6,
        ∀ k≤12,x • p.getVert k=p.getVert (12-k)) :
    ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (reflectionGroup c d.reflection)) 6 := by
  obtain ⟨_,_,K,fK,finK,chK,hK,e,_⟩ := hq
  let _ := fK
  let _ := finK
  let _ := chK
  intro a b p hp hl hT g hg hmove
  let D := halfPathActor (X := (A).Universal) p 6
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  have hv:Nat.card ((sourceGraph A).neighborSet (p.getVert 6))=Nat.card (K v.type)+1 := by
    rw [hval,hK]
    change (if (p.getVert 6).type then 9 else 3)=(if (p.getVert 6).type then 8 else 2)+1
    cases (p.getVert 6).type <;> rfl
  obtain ⟨_,_,z,hR,hV⟩ := source_six_root_coordinates h c d p hp hl hT (e v) hv
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl (e v))
  have hker := source_six_halfPathLinearMap_kernel h c d p hp hl hT (e v) hv
  have hfi:Function.Injective f := (f.ker_eq_bot_iff).mp (by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective,hker,hzero d p hp hl hT])
  have hsupp := source_six_halfPathActor_supplement h c d p hp hl hT (e v) hv
  have hCD := SourceHalfPathTorus.local_cartan_le_halfactor h c d p hl hT hsupp
  have hdiag := Assembly.BTwoSource.six_actor_full_diagonal h c d.reflection d.normalizes
    p hl hT hCD (e v) z hR hV
  obtain ⟨x,hx,hrev⟩ := href p hp hl hT
  have hfix:cartan c≤pathFixer (X := (A).Universal) p := by
    intro y hy k _
    exact reflectionApartment_fixed c d.reflection d.normalizes y hy _ (hT _ (p.getVert_mem_support k))
  have hfac := apartment_path_factorization h c 6 (by decide) d.reflection d.fixes d.moves
    d.squares d.normalizes d.transitive d.thick (p.drop 6)
    (by rw [Walk.drop_length,hl];decide) (by
      intro y hy
      rw [Walk.drop_support_eq_support_drop_min] at hy
      exact hT y (List.mem_of_mem_drop hy))
  apply halfFixer_exchange_of_faithful_coordinates p 6 hl (cartan c) D hfix hfac
    le_sup_left f hfi ?_ ?_ ?_ hdiag ⟨x,hx⟩ hrev g hg hmove
  · intro y hy
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent (K v.type) (f y)).mp
      (hR ▸ mem_map_of_mem f hy)
    exact ⟨a,ha.symm⟩
  · intro y hy
    obtain ⟨a,ha⟩ := (hV (f y)).mp (mem_map_of_mem f hy)
    exact ⟨a,ha.symm⟩
  · intro a
    obtain ⟨y,hy,he⟩ := (hV (NaturalCubic.lower a)).mpr ⟨a,rfl⟩
    exact ⟨y,hy,he⟩
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

set_option maxHeartbeats 800000 in
/-- The original mixed source constructs actual six-path apartment exchange.
The full actor cores, canonical quotient marks, and reversing reflections are
all supplied by the original subgroup geometry. -/
theorem source_apartment_exchange
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    ∃ d : SixPathSmallActorGeometry c,
      ChosenApartmentExchange (X := (reducedAmalgam Lₛ Sₛ).Universal)
        (sourceGraph (reducedAmalgam Lₛ Sₛ))
        (cartanApartment (reducedAmalgam Lₛ Sₛ) (reflectionGroup c d.reflection)) 6 := by
  obtain ⟨d,href⟩ := SourceApartmentReflections.source_apartment_reflections
    hG T hempty hM hu hmany hcard e H hH eR c
  refine ⟨d,faithful_exchange_of_reflections (L := Lₛ) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap c d
    (SourceHalfPathQuotients.source_half_path_quotients hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    (SourceHalfActorFaithful.source_half_actor_faithful hG T hempty hM hu hmany hcard e H hH eR c)
    href⟩
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceApartmentExchange
