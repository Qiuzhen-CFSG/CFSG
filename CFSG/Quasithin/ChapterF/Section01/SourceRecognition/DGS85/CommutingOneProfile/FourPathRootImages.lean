module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathFactorization
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicRootImagesGeneral
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentNeighborLiftingGeneral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.GeometricQuotient
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphCycles
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphAction
public import Theory.Combinatorics.SimpleGraph.GeneralizedQuadrangle.RootRigidity
public import Theory.GroupAction.RankTwoCosetGeometry.Distance

/-!
# The raw four-path quotient is a thick generalized quadrangle

The apartment relation preserves vertex types. Separation and neighbor lifting
transfer short-path uniqueness from the universal tree, while apartment
shortening gives diameter four. The original source valence supplies thickness.
Apply root rigidity directly to this raw class graph, before any BN-pair,
with the literal global class action. Matching an exit then identifies the
periodic images of the actual path radicals. A half-apartment translate gives
the signed representatives in the whole original Borel image, on the same
quotient map. The elementary source consumer discharges interior-star fixation,
separation and neighbor lifting.

Source: DGS, *Groups and Graphs* (1985), (3.6)--(3.7), pp.77--80; (14.1)--(14.2), pp.210--211.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open SimpleGraph SimpleGraph.Walk
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
universe u
variable {P B R : Type u} [Group P] [Group B] [Group R]
variable (A : RankTwoAmalgam P B R) (T : Set (SourceVertex A))
local notation "r" => sourceRelation A T 4
local notation "Δ" => classGraph (sourceGraph A) r

private theorem four_relation_same_type {a b : SourceVertex A} (hab : r a b) : a.type=b.type := by
  induction hab with
  | rel a b hab =>
    obtain ⟨p, _, hlen, _⟩ := hab
    exact (RankTwo.even_walk_iff _ p).mp (by rw [hlen]; decide)
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private def four_class_color : Quotient r → Bool :=
  Quotient.lift (fun a : SourceVertex A => a.type) (fun _ _ hh => four_relation_same_type A T hh)

private theorem four_class_color_adj {a b : Quotient r} (hab : (Δ).Adj a b) :
    four_class_color A T a ≠ four_class_color A T b := by
  obtain ⟨_,a,b,rfl,rfl,hab⟩ := hab
  exact hab.1

private theorem four_class_connected
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hsep : Separated r (sourceGraph A) 8) : (Δ).Connected := by
  exact (Universal.cosetGraph_isTree A hL hR).connected.map
    (classGraphMap hsep (by decide)) Quotient.mk_surjective

private theorem four_class_diameter
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hsep : Separated r (sourceGraph A) 8)
    (hdeg : TwoNeighborsIn (sourceGraph A) T)
    (hcover : ApartmentsCover (X := (A).Universal) (sourceGraph A) T 5)
    (a b : Quotient r) : (Δ).dist a b ≤ 4 := by
  let tree := Universal.cosetGraph_isTree A hL hR
  have hext : ApartmentExtension (X := A.Universal) (sourceGraph A) T 4 :=
    apartmentExtension_of_cover (X := A.Universal)
    (Γ := sourceGraph A) (T := T) tree.isAcyclic (source_action A) hdeg
    (by decide : 0<4) hcover
  obtain ⟨p,hp⟩ := classGraph_bounded_walks tree.connected hsep (by decide) 4
    (fun a => exists_bounded_representative (sourceGraph A) r a 4
      (apartment_shortening tree.connected hext a)) a b
  exact (dist_le p).trans hp

private theorem four_class_thickness
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hval : ∀ v : SourceVertex A, 3 ≤ Nat.card ((sourceGraph A).neighborSet v))
    (hsep : Separated r (sourceGraph A) 8)
    (hlift : NeighborLifting (sourceGraph A) r) :
    ∀ v a b : Quotient r, ∃ z, (Δ).Adj v z ∧ z≠a ∧ z≠b := by
  intro v a b
  obtain ⟨v,rfl⟩ := Quotient.exists_rep v
  have hcard : 3 ≤ Nat.card ((Δ).neighborSet (Quotient.mk r v)) := by
    let f := classGraphMap hsep (by decide : 1 < 8)
    have heq : Nat.card ((sourceGraph A).neighborSet v) =
        Nat.card ((Δ).neighborSet (Quotient.mk r v)) :=
      Nat.card_congr (Equiv.ofBijective (f.mapNeighborSet v)
        (classGraph_neighbor_bijective
          (Universal.cosetGraph_isTree A hL hR).connected hsep (by decide) hlift v))
    rw [← heq]
    exact hval v
  have hp : ({a,b} : Set (Quotient r)).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le a ({b} : Set (Quotient r))
  have hncard : 3 ≤ ((Δ).neighborSet (Quotient.mk r v)).ncard := by
    rw [←Nat.card_coe_set_eq]
    exact hcard
  obtain ⟨z,hz,hzne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (by omega :
    ({a,b} : Set (Quotient r)).ncard < ((Δ).neighborSet (Quotient.mk r v)).ncard)
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hzne
  exact ⟨z,hz,hzne.1,hzne.2⟩

/-- The raw apartment class graph has generalized-quadrangle geometry. -/
def four_class_geometry
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hsep : Separated r (sourceGraph A) 8)
    (hlift : NeighborLifting (sourceGraph A) r)
    (hdeg : TwoNeighborsIn (sourceGraph A) T)
    (hcover : ApartmentsCover (X := (A).Universal) (sourceGraph A) T 5) :
    SimpleGraph.GeneralizedQuadrangle.Geometry Δ where
  color := four_class_color A T
  color_adj := four_class_color_adj A T
  connected := four_class_connected A T hL hR hsep
  diameter := four_class_diameter A T hL hR hsep hdeg hcover
  short_paths := classGraph_short_paths_unique
    (Universal.cosetGraph_isTree A hL hR) hsep hlift

/-- Fixing three interior stars and one exit kills the original class action. -/
theorem four_class_root_rigidity
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hval : ∀ v : SourceVertex A, 3 ≤ Nat.card ((sourceGraph A).neighborSet v))
    (hsep : Separated r (sourceGraph A) 8)
    (hlift : NeighborLifting (sourceGraph A) r)
    (hdeg : TwoNeighborsIn (sourceGraph A) T)
    (hcover : ApartmentsCover (X := (A).Universal) (sourceGraph A) T 5)
    {a b : Quotient r} (p : (Δ).Walk a b) (hp : p.IsPath) (hlen : p.length = 4)
    (g : (A).Universal)
    (hstars : ∀ j, 0 < j → j < 4 → ∀ z, (Δ).Adj (p.getVert j) z →
      quotientAction r (apartmentSetoid_invariant (source_action A)) g z = z)
    (z : Quotient r) (hadj : (Δ).Adj b z) (hprev : z ≠ p.getVert 3)
    (hfix : quotientAction r (apartmentSetoid_invariant (source_action A)) g z = z) :
    ∀ v, quotientAction r (apartmentSetoid_invariant (source_action A)) g v = v := by
  let f : Δ ≃g Δ :=
    { toEquiv := quotientAction r (apartmentSetoid_invariant (source_action A)) g
      map_rel_iff' := quotientAction_adj_iff (apartmentSetoid_invariant (source_action A))
        (source_action A) g _ _ }
  exact (four_class_geometry A T hL hR hsep hlift hdeg hcover).root_rigidity
    (four_class_thickness A T hL hR hval hsep hlift) f p hp hlen hstars z hadj hprev hfix

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open Theory.GroupAction.CubicTree
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SimpleGraph SimpleGraph.Walk
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
variable (n : ℕ) (hn : 1<n)
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
  base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (htsq : ∀ i, t i*t i=1)
variable (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
  (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
  z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
  z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
local notation "A" => reducedAmalgam L S
local notation "ρ" => pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick
local notation "N" => apartmentGroup c ρ
local notation "T" => cartanApartment A N
local notation "hL" => inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 0)
local notation "hR" => inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 1)
local notation "ha" => pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick
local notation "hb" => pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick
local notation "l" => cartanLine A ρ ha hb hL hR

/-- The same line oriented from either original endpoint toward the other. -/
private def signRootLine (i : Bool) : Line (sourceGraph A) :=
  if i then
    { vertex j := (l).vertex (1-j)
      injective := fun _ _ he => by have hh := (l).injective he; omega
      adjacent j := by
        have hh := ((l).adjacent (1-(j+1))).symm
        convert hh using 1
        congr 1
        omega }
  else l

private theorem signRootLine_zero (i : Bool) :
    (signRootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex 0=
      base (Universal.cosetFamily A) i := by
  cases i
  · exact cartanLine_zero A ρ ha hb hL hR
  · change (l).vertex (1-0)=_
    simpa only [sub_zero] using cartanLine_one A ρ ha hb hL hR

private theorem signRootLine_one (i : Bool) :
    (signRootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex 1=
      base (Universal.cosetFamily A) (!i) := by
  cases i
  · exact cartanLine_one A ρ ha hb hL hR
  · change (l).vertex (1-1)=_
    simpa only [sub_self,Bool.not_true] using cartanLine_zero A ρ ha hb hL hR

private theorem signRootLine_range (i : Bool) :
    Set.range (signRootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex=T := by
  have he := cartanApartment_eq_line A ρ ha hb hL hR N (cartan c)
    (reflection_mem_apartmentGroup c ρ) (cartan_le c)
    (apartmentGroup_normalizes c ρ (pathRoots_normalizes h c n hn t htfix htmove htsq htnorm htrans hthick))
    le_rfl (pathRoots_square h c n hn t htfix htmove htsq htnorm htrans hthick)
  rw [he]
  cases i
  · rfl
  · change Set.range (fun j : ℤ => (l).vertex (1-j))=Set.range (l).vertex
    ext v
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨1-j,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨1-j,congrArg (l).vertex (sub_sub_cancel 1 j)⟩

private theorem signRootLine_reflection (i : Bool) (j : ℤ) :
    t i • (signRootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex j=
      (signRootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex (-j) := by
  cases i
  · exact alternatingVertex_left_reflection (htfix false) (htfix true) (htsq false) (htsq true) j
  · have hh := alternatingVertex_right_reflection (htfix false) (htfix true)
      (htsq false) (htsq true) (1-j)
    change t true • alternatingVertex (t true*t false)
      (base (Universal.cosetFamily A) false) (base (Universal.cosetFamily A) true) (1-j)=_
    rw [hh]
    congr 1
    omega

/-- Global root signs from the actual interior-star theorem and raw root rigidity. -/
theorem four_pathRoots_global_sign_of_root_rigidity
    (hsep : Separated (sourceRelation A T n) (sourceGraph A) (2*n))
    (hlift : NeighborLifting (sourceGraph A) (sourceRelation A T n))
    (hn4 : n = 4)
    (hstars : ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath →
      ∀ u ∈ pathRoot (X := (A).Universal) p, ∀ j, 0 < j → j < p.length →
      ∀ z, (sourceGraph A).Adj (p.getVert j) z → u • z = z)
    (hrigid : ∀ {a b : Quotient (sourceRelation A T n)}
      (p : (classGraph (sourceGraph A) (sourceRelation A T n)).Walk a b),
      p.IsPath → p.length = 4 → ∀ g : (A).Universal,
      (∀ j, 0 < j → j < 4 → ∀ z,
        (classGraph (sourceGraph A) (sourceRelation A T n)).Adj (p.getVert j) z →
        quotientAction (sourceRelation A T n) (apartmentSetoid_invariant (source_action A)) g z = z) →
      ∀ z, (classGraph (sourceGraph A) (sourceRelation A T n)).Adj b z → z ≠ p.getVert 3 →
      quotientAction (sourceRelation A T n) (apartmentSetoid_invariant (source_action A)) g z = z →
      ∀ v, quotientAction (sourceRelation A T n) (apartmentSetoid_invariant (source_action A)) g v = v)
    (i : Bool) (x : (A).Universal) (hx : x ∈ N) :
    (∀ u ∈ (ρ i).root, quotientMap A T n (x⁻¹*u*x) ∈
      (originalMiddle A).map (quotientMap A T n)) ∨
    (∀ u ∈ (ρ i).root, quotientMap A T n ((t i*x)⁻¹*u*(t i*x)) ∈
      (originalMiddle A).map (quotientMap A T n)) := by
  let li := signRootLine h c n hn t htfix htmove htsq htnorm htrans hthick i
  let tree := Universal.cosetGraph_isTree A hL hR
  have hperiod (j : ℤ) : sourceRelation A T n (li.vertex (j+8)) (li.vertex j) := by
    change apartmentSetoid (X := (A).Universal) (sourceGraph A) T n _ _
    rw [←signRootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
    have hn8 : 2*n=8 := by omega
    simpa only [hn8, Nat.cast_ofNat] using apartment_line_period (X := (A).Universal) tree.isAcyclic li n j
  have hsep8 : Separated (sourceRelation A T n) (sourceGraph A) 8 := by
    have he : 2*n=8 := by omega
    rw [←he]
    exact @hsep
  have htrans5 : BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 := by
    rw [show 5=n+1 by omega]
    exact htrans
  have hroot : ∀ d : ℤ, d % 8 = 0 →
      (pathRoot (X := (A).Universal) (lineSegment li 0 4)).map (quotientMap A T n) ≤
        (pathRoot (X := (A).Universal) (lineSegment li d 4)).map (quotientMap A T n) := by
    intro d hd
    rintro _ ⟨u, hu, rfl⟩
    let p := lineSegment li 0 4
    let q := lineSegment li d 4
    have hqT : ∀ z ∈ q.support, z ∈ T := by
      rw [←signRootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
      exact lineSegment_support li d 4
    have hqprev : q.penultimate = li.vertex (d+3) := by
      simp only [q, penultimate, lineSegment_length]
      exact lineSegment_getVert li d 4 3 (by decide)
    have he : (sourceGraph A).Adj (li.vertex (d+4)) (li.vertex (d+5)) := by
      convert li.adjacent (d+4) using 1
      congr 1
      omega
    have heprev : li.vertex (d+5) ≠ q.penultimate := by
      rw [hqprev]
      intro hh
      have := li.injective hh
      omega
    apply pathRoot_image_mem_of_same_classes_of_length 4 (by decide) (apartmentSetoid_invariant (source_action A))
      tree (source_action A) hsep8 hlift hrigid p q (lineSegment_isPath tree.isAcyclic li 0 4)
      (lineSegment_length _ _ _) (lineSegment_length _ _ _) ?_ ?_ ?_
      (li.vertex (d+5)) he heprev ?_ u hu
    · intro j hj
      rw [lineSegment_getVert li 0 4 j hj, lineSegment_getVert li d 4 j hj]
      apply (line_related_iff_mod tree.isAcyclic li (sourceRelation A T n) 8
        (by decide) hsep8 hperiod _ _).mpr
      change (0+(j:ℤ)) % 8 = (d+j) % 8
      rw [zero_add,Int.add_emod,hd,zero_add,Int.emod_emod]
    · intro v hv j hj hjl z hz
      exact hstars p (lineSegment_isPath tree.isAcyclic li 0 4) v hv j hj
        (by simpa only [p, lineSegment_length] using hjl) z hz
    · intro v hv j hj hjl z hz
      exact hstars q (lineSegment_isPath tree.isAcyclic li d 4) v hv j hj
        (by simpa only [q, lineSegment_length] using hjl) z hz
    · have hqtrans : BasedPathTransitive (X := (A).Universal) (sourceGraph A) (q.length + 1) := by
        rw [show q.length + 1 = 5 by simp only [q, lineSegment_length]]
        exact @htrans5
      apply pathRoot_transitive_exits (X := (A).Universal) tree.isAcyclic q (lineSegment_isPath tree.isAcyclic li d 4)
        hqtrans (cartan c) he heprev
      · intro k hk
        apply reflectionApartment_fixed c t htnorm k hk
        change li.vertex (d+5) ∈ T
        rw [←signRootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
        exact ⟨d+5,rfl⟩
      · exact apartment_path_factorization h c n hn t htfix htmove htsq htnorm htrans hthick
          q (by rw [lineSegment_length]; decide) hqT
  have hB (g : (A).Universal) (hg₀ : g • li.vertex 0 = li.vertex 0)
      (hg₁ : g • li.vertex 1 = li.vertex 1) : g ∈ originalMiddle A := by
    rw [signRootLine_zero] at hg₀
    rw [signRootLine_one] at hg₁
    rw [originalMiddle, ←Universal.overlap_eq A hL hR]
    have hgf : g ∈ Universal.cosetFamily A i := by
      rw [←stabilizer_base (F := Universal.cosetFamily A) (i := i)]
      exact hg₀
    have hgt : g ∈ Universal.cosetFamily A (!i) := by
      rw [←stabilizer_base (F := Universal.cosetFamily A) (i := !i)]
      exact hg₁
    cases i
    · exact ⟨hgf,hgt⟩
    · exact ⟨hgt,hgf⟩
  have hli (j : ℤ) : x • li.vertex j ∈ Set.range li.vertex := by
    rw [signRootLine_range]
    apply cartanApartment_preserves A N hx
    rw [←signRootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
    exact ⟨j,rfl⟩
  obtain ⟨j,hj⟩ := hli 0
  obtain ⟨k,hk⟩ := hli 1
  have hadj : (sourceGraph A).Adj (li.vertex j) (li.vertex k) := by
    rw [hj,hk]
    exact source_action A x (li.adjacent 0)
  have hs := periodic_root_image_sign_of_length tree.isAcyclic li 4 (by decide) (quotientMap A T n) (originalMiddle A)
    hB hroot (t i) (signRootLine_reflection h c n hn t htfix htmove htsq htnorm htrans hthick i)
    x j k hj.symm hk.symm hadj
  have hroot0 : (ρ i).root = pathRoot (X := (A).Universal) (lineSegment li 0 4) := by
    let p := reflectionPath c t htfix htmove htnorm n (Nat.zero_lt_of_lt hn) i
    have hvertices := path_on_line_getVert tree.isAcyclic li p.walk.reverse p.isPath.reverse (by
      intro z hz
      rw [signRootLine_range]
      exact p.supported z (by simpa only [support_reverse,List.mem_reverse] using hz))
      (signRootLine_zero h c n hn t htfix htmove htsq htnorm htrans hthick i).symm (by
        rw [getVert_reverse]
        exact p.previous.trans
          (signRootLine_one h c n hn t htfix htmove htsq htnorm htrans hthick i).symm)
    have hh := pathRoot_map_conj p.walk.reverse (lineSegment li 0 4) (1 : (A).Universal)
      (by rw [length_reverse,p.length_eq,hn4,lineSegment_length]) (by
        intro j hj
        rw [one_smul,hvertices j hj,lineSegment_getVert li 0 4 j (by simpa [p.length_eq,hn4] using hj),zero_add])
    have hconj : (MulAut.conj (1 : (A).Universal)).toMonoidHom = MonoidHom.id _ := by
      ext z
      simp
    rw [hconj,Subgroup.map_id] at hh
    change pathRoot (X := (A).Universal) p.walk = _
    simpa only [pathRoot, pathFixer_reverse] using hh
  simpa only [hroot0] using hs

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
