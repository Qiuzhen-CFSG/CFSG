module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorContainment
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathExistence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Neighborhood
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Theory.GroupTheory.WeakBNPair.RegularTree.OppositeRootCore

/-!
# The actual half-path actor's two-core lies in the midpoint two-core

The two six-path radicals act transitively on complementary subsets of the
midpoint star. Odd seven-path fixers and thickness give odd valence, so the
normal two-core of their join fixes the whole star. DGS (6.2)(d), transported
through the original universal-to-reduced covering, puts this two-subgroup
in the vertex two-core. The proof uses the covering's isomorphism on each
vertex stabilizer; it never identifies the full local kernel with O₂.

This discharges the separate own-core placement premise of the genuine
small-actor exchange consumer, for both endpoint orientations and the same
literal half-path radicals. The (14.9)(c) natural-coordinate profile remains
an explicit source input. In particular this does not prove the exhaustive
(14.9) alternatives or the suitable reflection choices of (14.17).

Source: DGS, *Groups and Graphs* (1985), (6.2)(d), p.119;
(14.1), (14.3), (14.9), (14.12), (14.17), pp.210--212,215--218,221.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
open scoped Pointwise

namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open RankTwoAmalgam Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original Sylow-kernel theorem transports through the literal tree cover. -/
theorem universal_two_subgroup_le_core_of_neighbors (h : HypothesisF11 L S)
    (v : SourceVertex (reducedAmalgam L S)) (H : Subgroup (reducedAmalgam L S).Universal)
    (hH : IsPGroup 2 H) (hHv : H ≤ MulAction.stabilizer _ v)
    (hfix : ∀ x∈H, ∀ w, (sourceGraph (reducedAmalgam L S)).Adj v w → x • w=w) :
    H ≤ (MulAction.stabilizer (reducedAmalgam L S).Universal v).pCoreIn 2 := by
  let cov := bOne_tree_cover h
  let f := bOne_tree_map h
  let F := reducedFamily L S
  have hmap : H.map f ≤ U F (cov.vertex v) := by
    rintro _ ⟨x,hx,rfl⟩ w hw
    rcases (RankTwo.mem_ball_one F (cov.vertex v) w).mp hw with hw | rfl
    · obtain ⟨u,hu⟩ := (cov.neighbor_bijective v).2 ⟨w,hw⟩
      have he : cov.vertex u.val=w := congrArg Subtype.val hu
      rw [←he,←cov.vertex_smul,hfix x hx u.val u.property]
    · rw [←cov.vertex_smul,hHv hx]
  have hQ := CommutingNontrivial.pSubgroup_le_Q_of_le_U F (cov.vertex v) (H.map f)
    (hH.map f) hmap (reduced_kernel_sylow h _)
  let P := RankTwo.stabilizer (Universal.cosetFamily (reducedAmalgam L S)) v
  let P' := RankTwo.stabilizer F (cov.vertex v)
  let e : P ≃* P' := cov.stabilizerEquiv v
  have he : (P.pCoreIn 2).map f = Q F (cov.vertex v) := by
    change ((pCore 2 P).map P.subtype).map f = (pCore 2 P').map P'.subtype
    rw [Subgroup.map_map]
    have hcomp : f.comp P.subtype = P'.subtype.comp e.toMonoidHom := rfl
    rw [hcomp,←Subgroup.map_map,pCore_map_iso]
  intro x hx
  have hmem := hQ (mem_map_of_mem f hx)
  rw [←he] at hmem
  obtain ⟨y,hy,hxy⟩ := hmem
  have heq : (⟨y,pCoreIn_le 2 P hy⟩ : P) = ⟨x,hHv hx⟩ :=
    e.injective (Subtype.ext hxy)
  have hyx : y=x := congrArg Subtype.val heq
  rw [←hyx]
  exact hy
/-- Every supported twelve-path has its actual half-path actor core in the midpoint core. -/
theorem source_six_halfPathActor_core_le_midpoint_core
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hlen : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) :
    (halfPathActor (X := (reducedAmalgam L S).Universal) p 6).pCoreIn 2 ≤
      (MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert 6)).pCoreIn 2 := by
  let A := reducedAmalgam L S
  let l := p.take 6
  let r := (p.drop 6).reverse
  have hl : l.length=6 := by simp only [l,take_length,hlen]; decide
  have hr : r.length=6 := by simp only [r,length_reverse,drop_length,hlen]
  have hlnil : ¬l.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hrnil : ¬r.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hprevl : l.penultimate=p.getVert 5 := by
    simp only [penultimate,hl,l,take_getVert]; rfl
  have hprevr : r.penultimate=p.getVert 7 := by
    simp only [penultimate,hr,r,getVert_reverse,drop_length,hlen,drop_getVert]
  have hdiff : l.penultimate≠r.penultimate := by
    rw [hprevl,hprevr]
    intro he
    have := hp.getVert_injOn (by omega : 5≤p.length) (by omega : 7≤p.length) he
    omega
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hTl : ∀ z∈l.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    intro z hz
    rw [support_take] at hz
    exact hT z (List.mem_of_mem_take hz)
  have hTr : ∀ z∈r.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    intro z hz
    simp only [r,support_reverse,List.mem_reverse] at hz
    rw [drop_support_eq_support_drop_min] at hz
    exact hT z (List.mem_of_mem_drop hz)
  have hK (z) (hz : z∈cartanApartment A (reflectionGroup c d.reflection)) :
      ∀ k∈cartan c, k • z=z :=
    fun k hk => reflectionApartment_fixed c d.reflection d.normalizes k hk z hz
  have hfac (u v) (q : (sourceGraph A).Walk u v) (hqpos : 0<q.length)
      (hqT : ∀ z∈q.support, z∈cartanApartment A (reflectionGroup c d.reflection)) :=
    apartment_path_factorization h c 6 (by decide) d.reflection d.fixes d.moves d.squares
      d.normalizes d.transitive d.thick q hqpos hqT
  have hval : 3≤Nat.card ((sourceGraph A).neighborSet (p.getVert 6)) := by
    let cov := bOne_tree_cover h
    rw [Nat.card_congr (Equiv.ofBijective (cov.hom.mapNeighborSet (p.getVert 6))
      (cov.neighbor_bijective (p.getVert 6)))]
    rw [RankTwo.card_neighbors_of_indices (reducedFamily L S)
      (fun j => ((reducedFamily L S (!j)).subgroupOf (reducedFamily L S j)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) _
  have : Finite ((sourceGraph A).neighborSet (p.getVert 6)) :=
    Nat.finite_of_card_ne_zero (by omega)
  have hnew : r.penultimate∉l.support := by
    intro hm
    exact hdiff.symm (htree.eq_penultimate_of_adj_end (hp.take 6) (r.adj_penultimate hrnil).symm hm)
  have hodd := d.odd (l.concat (r.adj_penultimate hrnil).symm)
    ((hp.take 6).concat hnew _) (by rw [length_concat,hl])
  have hfix := opposite_pathRoots_core_fixes_neighbors htree (source_action A)
    l r (hp.take 6) (hp.drop 6).reverse hlnil hrnil hdiff hval
    (by rw [hl]; exact d.transitive) (by rw [hr]; exact d.transitive) (cartan c)
    (hK _ (hTl _ (l.getVert_mem_support _))) (hK _ (hTr _ (r.getVert_mem_support _)))
    (hfac _ _ l (by omega) hTl) (hfac _ _ r (by omega) hTr) hodd
  have hjoin : pathRoot (X := A.Universal) l ⊔ pathRoot (X := A.Universal) r =
      halfPathActor (X := A.Universal) p 6 := by
    dsimp only [r]
    rw [pathRoot_reverse,sup_comm]
  rw [hjoin] at hfix
  exact universal_two_subgroup_le_core_of_neighbors h (p.getVert 6) _
    (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans (halfPathActor_le_midpoint_stabilizer (by omega))) hfix

universe uF
/-- The smaller natural coordinates imply exchange with the core placement proved above. -/
theorem source_six_small_actor_exchange_of_coordinates
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    (hlocal : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) →
      ∀ g : (reducedAmalgam L S).Universal,
      (∀ k, 6≤k → k≤12 → g • p.getVert k=p.getVert k) → g • a≠a →
      (¬∃ z : (reducedAmalgam L S).Universal,
        (∀ k≤6, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b) →
      Nonempty (SmallActorPathCoordinates.{uF} p 6 (cartan c))) :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) 6 := by
  apply source_six_small_actor_exchange h c d
  intro a b p hp hl hT g hg hm hfail
  exact ⟨source_six_halfPathActor_core_le_midpoint_core h c d p hp hl hT,
    hlocal p hp hl hT g hg hm hfail⟩

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
