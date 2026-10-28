module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorCore
public import Theory.GroupTheory.WeakBNPair.RegularTree.OppositeRootQuotient
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearValence

/-!
# The literal half-path actor covers the midpoint linear quotient

Restrict the universal-to-reduced covering to the join of the two half-path
radicals. Each radical is a two-group in the midpoint stabilizer, so its
image lies in the intrinsic local actor. The covering is injective there.
Compose this restriction with the original local SL₂ marking. Its kernel
is a two-group and fixes the midpoint star. Root regularity and full field
valence give surjectivity; the trivial two-core of SL₂ identifies its
kernel with the smaller actor's own two-core.

This constructs the quotient part of (14.9)(c), with the original map on
every element. The natural action on that kernel, Cartan/root coordinates,
and suitable reflection choices remain separate source obligations.
Source: DGS, *Groups and Graphs* (1985), (14.1), (14.3)(a), (14.9)(c),
printed pp.210--212,215--216.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open RankTwoAmalgam Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S)
variable {a b : SourceVertex (reducedAmalgam L S)}
variable (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (n : ℕ) (hlen : p.length = 2*n)

include hlen in
/-- Both literal half-path radicals land in the intrinsic midpoint actor. -/
theorem halfPathActor_map_le_local :
    (halfPathActor (X := (reducedAmalgam L S).Universal) p n).map (bOne_tree_map h) ≤
      graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert n)) := by
  let A := halfPathActor (X := (reducedAmalgam L S).Universal) p n
  have hA := halfPathActor_le_midpoint_stabilizer (X := (reducedAmalgam L S).Universal) hlen
  have root_le (R : Subgroup (reducedAmalgam L S).Universal)
      (hRA : R ≤ A) (hR : IsPGroup 2 R) :
      R.map (bOne_tree_map h) ≤ graphLocalGroup (reducedFamily L S)
        ((bOne_tree_cover h).vertex (p.getVert n)) := by
    apply pGroup_le_sylowGenerated _ _ _ (hR.map _)
    rintro _ ⟨x,hx,rfl⟩
    change bOne_tree_map h x • (bOne_tree_cover h).vertex (p.getVert n) = _
    rw [←(bOne_tree_cover h).vertex_smul,hA (hRA hx)]
  rw [Subgroup.map_sup]
  exact sup_le (root_le _ le_sup_left (pathRoot_isTwo _))
    (root_le _ le_sup_right (pathRoot_isTwo _))

/-- The restriction is exactly the original universal-to-reduced map. -/
def halfPathLocalMap : halfPathActor (X := (reducedAmalgam L S).Universal) p n →*
    graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert n)) :=
  ((bOne_tree_map h).comp (halfPathActor (X := (reducedAmalgam L S).Universal) p n).subtype).codRestrict _
    (fun x => halfPathActor_map_le_local h p n hlen (mem_map_of_mem _ x.property))

/-- Local covering faithfulness makes the literal restriction injective. -/
theorem halfPathLocalMap_injective : Function.Injective (halfPathLocalMap h p n hlen) := by
  intro x y he
  have hA := halfPathActor_le_midpoint_stabilizer (X := (reducedAmalgam L S).Universal) hlen
  have hxy : bOne_tree_map h x = bOne_tree_map h y := congrArg Subtype.val he
  have he' := (bOne_tree_cover h).stabilizerEquiv (p.getVert n) |>.injective
    (a₁ := ⟨x,hA x.property⟩) (a₂ := ⟨y,hA y.property⟩) (Subtype.ext hxy)
  have hxy' := congrArg (fun z : RankTwo.stabilizer (Universal.cosetFamily (reducedAmalgam L S)) (p.getVert n) => (z : (reducedAmalgam L S).Universal)) he'
  exact Subtype.ext hxy'

variable {F : Type*} [Field F]
variable (e : (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert n)) ⧸
    pCore 2 (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert n)))) ≃* SL(2,F))

/-- The local marking restricted to the actual half-path actor. -/
def halfPathLinearMap : halfPathActor (X := (reducedAmalgam L S).Universal) p n →* SL(2,F) :=
  (e.toMonoidHom.comp (QuotientGroup.mk' _)).comp (halfPathLocalMap h p n hlen)

/-- Its kernel is exactly the inverse image of the original local two-core. -/
theorem halfPathLinearMap_kernel :
    (halfPathLinearMap h p n hlen e).ker =
      (pCore 2 (graphLocalGroup (reducedFamily L S)
        ((bOne_tree_cover h).vertex (p.getVert n)))).comap (halfPathLocalMap h p n hlen) := by
  ext x
  change e (QuotientGroup.mk' _ (halfPathLocalMap h p n hlen x)) = 1 ↔ _
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff _

/-- The original local two-core restricts to a two-group. -/
theorem halfPathLinearMap_kernel_isTwo : IsPGroup 2 (halfPathLinearMap h p n hlen e).ker := by
  rw [halfPathLinearMap_kernel]
  exact pCore_isPGroup.comap_of_injective _ (halfPathLocalMap_injective h p n hlen)

/-- Kernel elements fix every actual midpoint neighbor through the covering. -/
theorem halfPathLinearMap_kernel_fixes_neighbors
    (x : halfPathActor (X := (reducedAmalgam L S).Universal) p n)
    (hx : x ∈ (halfPathLinearMap h p n hlen e).ker)
    (w : SourceVertex (reducedAmalgam L S))
    (hw : (sourceGraph (reducedAmalgam L S)).Adj (p.getVert n) w) :
    (x : (reducedAmalgam L S).Universal) • w = w := by
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert n)
  let J := graphLocalGroup (reducedFamily L S) v
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  have hcore : J.pCoreIn 2 = Q (reducedFamily L S) v := sylowGenerated_core _
  have hxJ : halfPathLocalMap h p n hlen x ∈ pCore 2 J := by
    rw [halfPathLinearMap_kernel] at hx
    exact hx
  have hxQ : bOne_tree_map h x ∈ Q (reducedFamily L S) v :=
    hcore ▸ mem_map_of_mem J.subtype hxJ
  have hxv : (x : (reducedAmalgam L S).Universal) • p.getVert n = p.getVert n :=
    halfPathActor_le_midpoint_stabilizer hlen x.property
  have hfix : bOne_tree_map h x • cov.vertex w = cov.vertex w :=
    (source_Z_Q_U (reduced_triple h) v).2 hxQ _
      ((RankTwo.mem_ball_one _ _ _).mpr (Or.inl (cov.hom.map_adj hw)))
  apply congrArg Subtype.val ((cov.neighbor_bijective (p.getVert n)).1
    (a₁ := ⟨(x : (reducedAmalgam L S).Universal) • w,by
      change (sourceGraph (reducedAmalgam L S)).Adj (p.getVert n) ((x : (reducedAmalgam L S).Universal) • w)
      simpa only [hxv] using source_action (reducedAmalgam L S) (x : (reducedAmalgam L S).Universal) hw⟩)
    (a₂ := ⟨w,hw⟩) (Subtype.ext ?_))
  exact (cov.vertex_smul _ _).trans hfix

variable [Finite F] [CharP F 2]

/-- The literal local marking is surjective on the actual smaller actor. -/
theorem source_six_halfPathLinearMap_surjective
    (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hlen : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection))
    (e : (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,F))
    (hval : Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet (p.getVert 6)) = Nat.card F+1) :
    Function.Surjective (halfPathLinearMap h p 6 hlen e) := by
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
  have : Finite ((sourceGraph A).neighborSet (p.getVert 6)) :=
    Nat.finite_of_card_ne_zero (by rw [hval]; omega)
  have hnewr : r.penultimate∉l.support := by
    intro hm
    exact hdiff.symm (htree.eq_penultimate_of_adj_end (hp.take 6) (r.adj_penultimate hrnil).symm hm)
  have hnewl : l.penultimate∉r.support := by
    intro hm
    exact hdiff (htree.eq_penultimate_of_adj_end (hp.drop 6).reverse (l.adj_penultimate hlnil).symm hm)
  have hoddp := d.odd (l.concat (r.adj_penultimate hrnil).symm)
    ((hp.take 6).concat hnewr _) (by rw [length_concat,hl])
  have hoddq := d.odd (r.concat (l.adj_penultimate hlnil).symm)
    ((hp.drop 6).reverse.concat hnewl _) (by rw [length_concat,hr])
  have hjoin : pathRoot (X := A.Universal) l ⊔ pathRoot (X := A.Universal) r =
      halfPathActor (X := A.Universal) p 6 := by
    dsimp only [r]
    rw [pathRoot_reverse,sup_comm]
  let j := MulEquiv.subgroupCongr hjoin
  let f := (halfPathLinearMap h p 6 hlen e).comp j.toMonoidHom
  have hf : Function.Surjective f :=
    opposite_pathRoots_linear_surjective htree (source_action A)
      l r (hp.take 6) (hp.drop 6).reverse hlnil hrnil hdiff hval
      (by rw [hl]; exact d.transitive) (by rw [hr]; exact d.transitive) (cartan c)
      (hK _ (hTl _ (l.getVert_mem_support _))) (hK _ (hTr _ (r.getVert_mem_support _)))
      (hfac _ _ l (by omega) hTl) (hfac _ _ r (by omega) hTr) hoddp hoddq f
      (fun x hx w hw => halfPathLinearMap_kernel_fixes_neighbors h p 6 hlen e (j x) hx w hw)
  exact Function.Surjective.of_comp hf

/-- The kernel of this restriction is the smaller actor's own two-core. -/
theorem source_six_halfPathLinearMap_kernel
    (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hlen : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection))
    (e : (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,F))
    (hval : Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet (p.getVert 6)) = Nat.card F+1) :
    (halfPathLinearMap h p 6 hlen e).ker = pCore 2 (halfPathActor (X := (reducedAmalgam L S).Universal) p 6) := by
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  let J := graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))
  have : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have : Finite (halfPathActor (X := (reducedAmalgam L S).Universal) p 6) :=
    Finite.of_injective _ (halfPathLocalMap_injective h p 6 hlen)
  have hh := (halfPathLinearMap h p 6 hlen e).comap_pCore_of_ker_isPGroup
    (source_six_halfPathLinearMap_surjective h c d p hp hlen hT e hval)
    (halfPathLinearMap_kernel_isTwo h p 6 hlen e)
  simpa only [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot, MonoidHom.comap_bot] using hh

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hlen : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection))
    (e : (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,F))
    (hval : Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet (p.getVert 6)) = Nat.card F+1)

include c d hp hlen hT e hval in
/-- The two-root join supplements the original local core on the reduced side of the same cover. -/
theorem source_six_halfPathActor_supplement :
    (halfPathActor (X := (reducedAmalgam L S).Universal) p 6).map (bOne_tree_map h) ⊔
      Q (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) =
        graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) := by
  let J := graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))
  let f := halfPathLocalMap h p 6 hlen
  let q := QuotientGroup.mk' (pCore 2 J)
  have hsurj : Function.Surjective (q.comp f) := by
    intro z
    obtain ⟨x,hx⟩ := source_six_halfPathLinearMap_surjective h c d p hp hlen hT e hval (e z)
    exact ⟨x,e.injective hx⟩
  have hmap : f.range.map q = q.range := by
    rw [←MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hsurj,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hs : f.range ⊔ pCore 2 J = ⊤ := by
    have hh := (Subgroup.map_eq_range_iff.mp hmap).eq_top
    simpa only [q,QuotientGroup.ker_mk'] using hh
  have hh := congrArg (Subgroup.map J.subtype) hs
  have he : J.subtype.comp f = (bOne_tree_map h).comp
      (halfPathActor (X := (reducedAmalgam L S).Universal) p 6).subtype := rfl
  rw [Subgroup.map_sup,←MonoidHom.range_comp,he,MonoidHom.range_comp,range_subtype,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  have hcore : (pCore 2 J).map J.subtype = Q (reducedFamily L S)
      ((bOne_tree_cover h).vertex (p.getVert 6)) :=
    Theory.GroupTheory.AmalgamGraph.sylowGenerated_core _
  rwa [hcore] at hh

/-- The exact smaller two-core quotient carries the original local marking on representatives. -/
def sourceSixHalfPathQuotientEquiv :
    (halfPathActor (X := (reducedAmalgam L S).Universal) p 6 ⧸
      pCore 2 (halfPathActor (X := (reducedAmalgam L S).Universal) p 6)) ≃* SL(2,F) :=
  (QuotientGroup.quotientMulEquivOfEq
    (source_six_halfPathLinearMap_kernel h c d p hp hlen hT e hval).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (source_six_halfPathLinearMap_surjective h c d p hp hlen hT e hval))

/-- The isomorphism preserves the original covering and local quotient on each representative. -/
theorem sourceSixHalfPathQuotientEquiv_apply
    (x : halfPathActor (X := (reducedAmalgam L S).Universal) p 6) :
    sourceSixHalfPathQuotientEquiv h c d p hp hlen hT e hval (QuotientGroup.mk' _ x) =
      e (QuotientGroup.mk' _ (halfPathLocalMap h p 6 hlen x)) := rfl

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
