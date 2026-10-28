module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourcePathRoots
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicRootSigns
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# The two root signs on the actual source apartment classes

Orient the existing integer apartment from each original endpoint toward the
other. The canonical long path is forced by its first edge and the absence
of branching, so its genuine two-core fixes the whole corresponding half.
The literal apartment relation has period 2n on this same line. The modular
half-cycle argument then gives one sign for every element of each root.

This proves fixation of both marked vertex classes. It does not equate their
full stabilizer with the image of the original middle group. The existing
BN-pair-dependent class-stabilizer equality cannot supply that step here,
since it already assumes root signs in the original Borel image.

Source: DGS, *Groups and Graphs* (1985), proof of (3.7), printed p.80,
with the actual path roots of (14.1)--(14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open Theory.GroupAction.CubicTree
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
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
private def rootLine (i : Bool) : Line (sourceGraph A) :=
  if i then
    { vertex j := (l).vertex (1-j)
      injective := fun _ _ he => by have hh := (l).injective he; omega
      adjacent j := by
        have hh := ((l).adjacent (1-(j+1))).symm
        convert hh using 1
        congr 1
        omega }
  else l

private theorem rootLine_zero (i : Bool) :
    (rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex 0=
      base (Universal.cosetFamily A) i := by
  cases i
  · exact cartanLine_zero A ρ ha hb hL hR
  · change (l).vertex (1-0)=_
    simpa only [sub_zero] using cartanLine_one A ρ ha hb hL hR

private theorem rootLine_one (i : Bool) :
    (rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex 1=
      base (Universal.cosetFamily A) (!i) := by
  cases i
  · exact cartanLine_one A ρ ha hb hL hR
  · change (l).vertex (1-1)=_
    simpa only [sub_self,Bool.not_true] using cartanLine_zero A ρ ha hb hL hR

private theorem rootLine_range (i : Bool) :
    Set.range (rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex=T := by
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

private theorem rootLine_reflection (i : Bool) (j : ℤ) :
    t i • (rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex j=
      (rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex (-j) := by
  cases i
  · exact alternatingVertex_left_reflection (htfix false) (htfix true) (htsq false) (htsq true) j
  · have hh := alternatingVertex_right_reflection (htfix false) (htfix true)
      (htsq false) (htsq true) (1-j)
    change t true • alternatingVertex (t true*t false)
      (base (Universal.cosetFamily A) false) (base (Universal.cosetFamily A) true) (1-j)=_
    rw [hh]
    congr 1
    omega

private theorem pathRoots_fix_half (i : Bool) (u : (A).Universal) (hu : u∈(ρ i).root)
    (k : ℕ) (hk : k≤n) :
    u • (rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex k=
      (rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i).vertex k := by
  let p := reflectionPath c t htfix htmove htnorm n (Nat.zero_lt_of_lt hn) i
  let li := rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i
  have hvertices := path_on_line_getVert (Universal.cosetGraph_isTree A hL hR).isAcyclic
    li p.walk.reverse p.isPath.reverse (by
      intro z hz
      rw [rootLine_range]
      exact p.supported z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz))
    (rootLine_zero h c n hn t htfix htmove htsq htnorm htrans hthick i).symm (by
      rw [SimpleGraph.Walk.getVert_reverse]
      exact p.previous.trans (rootLine_one h c n hn t htfix htmove htsq htnorm htrans hthick i).symm)
  have huF : u∈pathFixer (X := (A).Universal) p.walk.reverse := by
    rw [pathFixer_reverse]
    exact Subgroup.pCoreIn_le 2 _ hu
  rw [←hvertices k (by rw [SimpleGraph.Walk.length_reverse,p.length_eq]; exact hk)]
  exact huF k (by rw [SimpleGraph.Walk.length_reverse,p.length_eq]; exact hk)

/-- On the literal source relation, the whole conjugate root fixes both
marked vertex classes for one of the two signs. No BN-pair or quotient
class-stabilizer identification is used. -/
theorem pathRoots_class_sign
    (hsep : Separated (sourceRelation A T n) (sourceGraph A) (2*n))
    (i : Bool) (x : (A).Universal) (hx : x∈N) :
    (∀ u∈(ρ i).root, ∀ j : Bool, sourceRelation A T n
      ((x⁻¹*u*x) • base (Universal.cosetFamily A) j)
      (base (Universal.cosetFamily A) j)) ∨
    (∀ u∈(ρ i).root, ∀ j : Bool, sourceRelation A T n
      (((t i*x)⁻¹*u*(t i*x)) • base (Universal.cosetFamily A) j)
      (base (Universal.cosetFamily A) j)) := by
  let li := rootLine h c n hn t htfix htmove htsq htnorm htrans hthick i
  have hperiod (j : ℤ) : sourceRelation A T n (li.vertex (j+(2*n:ℕ))) (li.vertex j) := by
    change apartmentSetoid (X := (A).Universal) (sourceGraph A) T n _ _
    rw [←rootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
    exact apartment_line_period (Universal.cosetGraph_isTree A hL hR).isAcyclic li n j
  have himage (j : ℤ) : x • li.vertex j∈Set.range li.vertex := by
    rw [rootLine_range]
    apply cartanApartment_preserves A N hx
    rw [←rootLine_range h c n hn t htfix htmove htsq htnorm htrans hthick i]
    exact ⟨j,rfl⟩
  obtain ⟨j,hj⟩ := himage 0
  obtain ⟨k,hk⟩ := himage 1
  have hadj : (sourceGraph A).Adj (li.vertex j) (li.vertex k) := by
    rw [hj,hk]
    exact source_action A x (li.adjacent 0)
  have hsign := line_root_class_sign (Universal.cosetGraph_isTree A hL hR).isAcyclic li
    (sourceRelation A T n) (apartmentSetoid_invariant (source_action A)) n
    (Nat.zero_lt_of_lt hn) hsep hperiod (ρ i).root
    (pathRoots_fix_half h c n hn t htfix htmove htsq htnorm htrans hthick i)
    (t i) (rootLine_reflection h c n hn t htfix htmove htsq htnorm htrans hthick i)
    x j k hj.symm hk.symm hadj
  have hconvert (g : (A).Universal) (u : (A).Universal)
      (he : sourceRelation A T n ((g⁻¹*u*g) • li.vertex 0) (li.vertex 0) ∧
        sourceRelation A T n ((g⁻¹*u*g) • li.vertex 1) (li.vertex 1)) :
      ∀ j : Bool, sourceRelation A T n ((g⁻¹*u*g) • base (Universal.cosetFamily A) j)
        (base (Universal.cosetFamily A) j) := by
    rw [rootLine_zero,rootLine_one] at he
    intro j
    cases i <;> cases j
    · exact he.1
    · exact he.2
    · exact he.2
    · exact he.1
  exact hsign.imp (fun he u hu => hconvert x u (he u hu))
    (fun he u hu => hconvert (t i*x) u (he u hu))
end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
