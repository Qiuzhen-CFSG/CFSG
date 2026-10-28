module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathFactorization
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicRootImages
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentNeighborLiftingGeneral

/-!
# Global Borel signs for the actual six-path roots

Match the actions of path radicals whose paths represent the same raw quotient
root. Interior-star fixation and rigidity after fixing one exit force equality
of their images under the global quotient map. Period-twelve coordinates then
place one of the two signed conjugates in the image of the original Borel.

This construction retains the literal `pathRoots`, `quotientMap` and the whole
`originalMiddle.map`. The raw geometric premises are discharged by the strict
source application, independently of the BN-pair that the signs will construct.
Source: DGS, *Groups and Graphs* (1985), (3.6)--(3.7), pp.77--80;
(14.1)--(14.2), pp.210--211.
-/

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
theorem pathRoots_global_sign_of_root_rigidity
    (hsep : Separated (sourceRelation A T n) (sourceGraph A) (2*n))
    (hlift : NeighborLifting (sourceGraph A) (sourceRelation A T n))
    (hn6 : n = 6)
    (hstars : ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath →
      ∀ u ∈ pathRoot (X := (A).Universal) p, ∀ j, 0 < j → j < p.length →
      ∀ z, (sourceGraph A).Adj (p.getVert j) z → u • z = z)
    (hrigid : ∀ {a b : Quotient (sourceRelation A T n)}
      (p : (classGraph (sourceGraph A) (sourceRelation A T n)).Walk a b),
      p.IsPath → p.length = 6 → ∀ g : (A).Universal,
      (∀ j, 0 < j → j < 6 → ∀ z,
        (classGraph (sourceGraph A) (sourceRelation A T n)).Adj (p.getVert j) z →
        quotientAction (sourceRelation A T n) (apartmentSetoid_invariant (source_action A)) g z = z) →
      ∀ z, (classGraph (sourceGraph A) (sourceRelation A T n)).Adj b z → z ≠ p.getVert 5 →
      quotientAction (sourceRelation A T n) (apartmentSetoid_invariant (source_action A)) g z = z →
      ∀ v, quotientAction (sourceRelation A T n) (apartmentSetoid_invariant (source_action A)) g v = v)
    (i : Bool) (x : (A).Universal) (hx : x ∈ N) :
    (∀ u ∈ (ρ i).root, quotientMap A T n (x⁻¹*u*x) ∈
      (originalMiddle A).map (quotientMap A T n)) ∨
    (∀ u ∈ (ρ i).root, quotientMap A T n ((t i*x)⁻¹*u*(t i*x)) ∈
      (originalMiddle A).map (quotientMap A T n)) := by
  let li := signRootLine h c n hn t htfix htmove htsq htnorm htrans hthick i
  let tree := Universal.cosetGraph_isTree A hL hR
  have hperiod (j : ℤ) : sourceRelation A T n (li.vertex (j+12)) (li.vertex j) := by
    change apartmentSetoid (X := (A).Universal) (sourceGraph A) T n _ _
    rw [←signRootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
    have hn12 : 2*n=12 := by omega
    simpa only [hn12, Nat.cast_ofNat] using apartment_line_period (X := (A).Universal) tree.isAcyclic li n j
  have hsep12 : Separated (sourceRelation A T n) (sourceGraph A) 12 := by
    have he : 2*n=12 := by omega
    rw [←he]
    exact @hsep
  have htrans7 : BasedPathTransitive (X := (A).Universal) (sourceGraph A) 7 := by
    rw [show 7=n+1 by omega]
    exact htrans
  have hroot : ∀ d : ℤ, d % 12 = 0 →
      (pathRoot (X := (A).Universal) (lineSegment li 0 6)).map (quotientMap A T n) ≤
        (pathRoot (X := (A).Universal) (lineSegment li d 6)).map (quotientMap A T n) := by
    intro d hd
    rintro _ ⟨u, hu, rfl⟩
    let p := lineSegment li 0 6
    let q := lineSegment li d 6
    have hqT : ∀ z ∈ q.support, z ∈ T := by
      rw [←signRootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
      exact lineSegment_support li d 6
    have hqprev : q.penultimate = li.vertex (d+5) := by
      simp only [q, penultimate, lineSegment_length]
      exact lineSegment_getVert li d 6 5 (by decide)
    have he : (sourceGraph A).Adj (li.vertex (d+6)) (li.vertex (d+7)) := by
      convert li.adjacent (d+6) using 1
      congr 1
      omega
    have heprev : li.vertex (d+7) ≠ q.penultimate := by
      rw [hqprev]
      intro hh
      have := li.injective hh
      omega
    apply pathRoot_image_mem_of_same_classes (apartmentSetoid_invariant (source_action A))
      tree (source_action A) hsep12 hlift hrigid p q (lineSegment_isPath tree.isAcyclic li 0 6)
      (lineSegment_length _ _ _) (lineSegment_length _ _ _) ?_ ?_ ?_
      (li.vertex (d+7)) he heprev ?_ u hu
    · intro j hj
      rw [lineSegment_getVert li 0 6 j hj, lineSegment_getVert li d 6 j hj]
      apply (line_related_iff_mod tree.isAcyclic li (sourceRelation A T n) 12
        (by decide) hsep12 hperiod _ _).mpr
      change (0+(j:ℤ)) % 12 = (d+j) % 12
      rw [zero_add,Int.add_emod,hd,zero_add,Int.emod_emod]
    · intro v hv j hj hjl z hz
      exact hstars p (lineSegment_isPath tree.isAcyclic li 0 6) v hv j hj
        (by simpa only [p, lineSegment_length] using hjl) z hz
    · intro v hv j hj hjl z hz
      exact hstars q (lineSegment_isPath tree.isAcyclic li d 6) v hv j hj
        (by simpa only [q, lineSegment_length] using hjl) z hz
    · have hqtrans : BasedPathTransitive (X := (A).Universal) (sourceGraph A) (q.length + 1) := by
        rw [show q.length + 1 = 7 by simp only [q, lineSegment_length]]
        exact @htrans7
      apply pathRoot_transitive_exits (X := (A).Universal) tree.isAcyclic q (lineSegment_isPath tree.isAcyclic li d 6)
        hqtrans (cartan c) he heprev
      · intro k hk
        apply reflectionApartment_fixed c t htnorm k hk
        change li.vertex (d+7) ∈ T
        rw [←signRootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
        exact ⟨d+7,rfl⟩
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
  have hs := periodic_root_image_sign tree.isAcyclic li (quotientMap A T n) (originalMiddle A)
    hB hroot (t i) (signRootLine_reflection h c n hn t htfix htmove htsq htnorm htrans hthick i)
    x j k hj.symm hk.symm hadj
  have hroot0 : (ρ i).root = pathRoot (X := (A).Universal) (lineSegment li 0 6) := by
    let p := reflectionPath c t htfix htmove htnorm n (Nat.zero_lt_of_lt hn) i
    have hvertices := path_on_line_getVert tree.isAcyclic li p.walk.reverse p.isPath.reverse (by
      intro z hz
      rw [signRootLine_range]
      exact p.supported z (by simpa only [support_reverse,List.mem_reverse] using hz))
      (signRootLine_zero h c n hn t htfix htmove htsq htnorm htrans hthick i).symm (by
        rw [getVert_reverse]
        exact p.previous.trans
          (signRootLine_one h c n hn t htfix htmove htsq htnorm htrans hthick i).symm)
    have hh := pathRoot_map_conj p.walk.reverse (lineSegment li 0 6) (1 : (A).Universal)
      (by rw [length_reverse,p.length_eq,hn6,lineSegment_length]) (by
        intro j hj
        rw [one_smul,hvertices j hj,lineSegment_getVert li 0 6 j (by simpa [p.length_eq,hn6] using hj),zero_add])
    have hconj : (MulAut.conj (1 : (A).Universal)).toMonoidHom = MonoidHom.id _ := by
      ext z
      simp
    rw [hconj,Subgroup.map_id] at hh
    change pathRoot (X := (A).Universal) p.walk = _
    simpa only [pathRoot, pathFixer_reverse] using hh
  simpa only [hroot0] using hs

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
