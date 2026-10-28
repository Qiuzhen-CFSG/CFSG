module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathRootSeparation
public import Theory.GroupTheory.CentralInvolutionProjection
public import Theory.GroupTheory.WeakBNPair.RegularTree.ReflectionChange
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphBalls

/-!
# Central reflection changes for the original six-path roots

The two original reflections identify the entire Cartan orbit apartment
with an explicit integer line. Every chosen reflection path follows those
same coordinates; this removes any dependence on its existential choice.

Given the central direct-product conclusion used on DGS p.222, project one
reflection into the root-generated factor. Its central correction is an
involution, the other reflection is unchanged, and both marked neighbor
images and the action on the whole compatible Cartan are preserved. Fixation
of the radius-three ball gives the common eight-vertex segment, hence
agreement of the first four vertices of the actual chosen paths.

The final consumer applies the previously proved branching contradiction
to the resulting six-path roots on the literal universal tree. It transfers
thickness from the original reflections and excludes each original-Borel
twist moving the second vertex. Both Boolean orientations are covered.

This constructs the reflection change from its precise earlier structural
premises. The actual r=6 quotient module, classification of invariant
complements, central splitting and center-ball containment still have to be
established from the original local profiles. Thus full (14.17), the binary
branches, corrected (14.14), and the TYPE2F4(2) exit in (14.19) remain open.
The separate r=4 quotient descent and Borel-sign family is not used here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(14.17), printed pp.221--223, especially the reflection change on p.222.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open Theory.GroupAction.CubicTree
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (c : CompatibleCartans L (reducedSylow L S))
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
  base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (htsq : ∀ i, t i * t i = 1)
variable (htnorm : ∀ i, t i ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include htfix htsq htnorm in
/-- The whole original Cartan orbit is the explicitly marked reflection line. -/
theorem reflectionApartment_eq_oriented_line (i : Bool) :
    cartanApartment (reducedAmalgam L S) (reflectionGroup c t) =
      Set.range (alternatingVertex (t (!i)*t i)
        (base (Universal.cosetFamily (reducedAmalgam L S)) i)
        (base (Universal.cosetFamily (reducedAmalgam L S)) (!i))) := by
  let A := reducedAmalgam L S
  let N := reflectionGroup c t
  let a := base (Universal.cosetFamily A) i
  let b := base (Universal.cosetFamily A) (!i)
  have he : cartanApartment A N = {v | ∃ g∈N, g • a=v ∨ g • b=v} := by
    ext v
    constructor
    · rintro ⟨g,hg,j,hj⟩
      refine ⟨g,hg,?_⟩
      by_cases hji : j=i
      · exact Or.inl (by simpa only [hji] using hj)
      · have hji' : j=(!i) := by cases i <;> cases j <;> simp_all
        exact Or.inr (by simpa only [hji'] using hj)
    · rintro ⟨g,hg,hh | hh⟩
      · exact ⟨g,hg,i,hh⟩
      · exact ⟨g,hg,!i,hh⟩
  rw [he]
  apply reflectionOrbit_eq_range (htfix i) (htfix (!i)) (htsq i) (htsq (!i))
    (cartan c) N (reflectionGroup_mem c t i) (reflectionGroup_mem c t (!i))
    (reflectionGroup_normalizes c t htnorm)
  · intro k hk
    exact ⟨reflectionApartment_fixed c t htnorm k hk a (cartanApartment_base A N i),
      reflectionApartment_fixed c t htnorm k hk b (cartanApartment_base A N (!i))⟩
  · apply Subgroup.closure_mono
    rintro g (hg | ⟨j,rfl⟩)
    · exact Or.inl hg
    · right
      by_cases hji : j=i
      · simp only [hji,Set.mem_insert_iff,Set.mem_singleton_iff,true_or]
      · have hji' : j=(!i) := by cases i <;> cases j <;> simp_all
        simp only [hji',Set.mem_insert_iff,Set.mem_singleton_iff,or_true]

include htfix htmove htsq htnorm in
/-- The actual chosen path has the same coordinates as the oriented reflection line. -/
theorem reflectionPath_reverse_getVert (n : ℕ) (hn : 0<n) (i : Bool)
    (k : ℕ) (hk : k≤n) :
    (reflectionPath c t htfix htmove htnorm n hn i).walk.reverse.getVert k =
      alternatingVertex (t (!i)*t i)
        (base (Universal.cosetFamily (reducedAmalgam L S)) i)
        (base (Universal.cosetFamily (reducedAmalgam L S)) (!i)) (k : ℤ) := by
  let A := reducedAmalgam L S
  let p := reflectionPath c t htfix htmove htnorm n hn i
  have ht := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hab : (sourceGraph A).Adj (base (Universal.cosetFamily A) i)
      (base (Universal.cosetFamily A) (!i)) :=
    ⟨by change i≠(!i); cases i <;> decide,incident_base _ _ _⟩
  let l := (localMoversTrack ht ⟨source_action A⟩ hab (htfix i) (htfix (!i))
    (htmove i) (by simpa only [Bool.not_not] using htmove (!i))).toLine
  have hfirst : p.walk.reverse.getVert 1=l.vertex 1 := by
    have hp : p.walk.reverse.getVert 1=base (Universal.cosetFamily A) (!i) := by
      rw [SimpleGraph.Walk.getVert_reverse]
      exact p.previous
    simpa only [l,Track.toLine,localMoversTrack_one] using hp
  apply path_getVert_eq_line ht l p.walk.reverse p.isPath.reverse
    (by simp only [l,localMoversTrack_zero]; rfl) hfirst ?_ k
    (by simpa only [SimpleGraph.Walk.length_reverse,p.length_eq] using hk)
  intro v hv
  have hh := p.supported v (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv)
  rw [reflectionApartment_eq_oriented_line c t htfix htsq htnorm i] at hh
  exact hh

include htfix htmove htsq htnorm in
/-- The central factor supplies a compatible replacement reflection and the
shared eight-vertex segment, including the actual chosen-path comparison. -/
theorem source_six_central_reflection_change
    (i : Bool) (J R : Subgroup (reducedAmalgam L S).Universal)
    (hRJ : R ≤ J) (hKJ : cartan c ≤ J)
    (hdis : centerIn J ⊓ R=⊥) (htprod : t i∈centerIn J ⊔ R)
    (hball : centerIn J ≤ graphBallFixer (sourceGraph (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 3) :
    ∃ (t' : Bool → (reducedAmalgam L S).Universal)
      (htfix' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
        base (Universal.cosetFamily (reducedAmalgam L S)) j)
      (htmove' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
      (_htsq' : ∀ j, t' j*t' j=1)
      (htnorm' : ∀ j, t' j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal)),
      t' i∈R ∧ t' (!i)=t (!i) ∧
      (∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) =
        t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j)) ∧
      (∃ z∈centerIn J, t i=z*t' i ∧ z*z=1) ∧
      (∀ k∈cartan c, t' i*k*(t' i)⁻¹=t i*k*(t i)⁻¹) ∧
      (∀ j : ℤ, -3≤j → j≤4 →
        let v := alternatingVertex (t (!i)*t i)
          (base (Universal.cosetFamily (reducedAmalgam L S)) i)
          (base (Universal.cosetFamily (reducedAmalgam L S)) (!i)) j
        v ∈ cartanApartment (reducedAmalgam L S) (reflectionGroup c t) ∩
          cartanApartment (reducedAmalgam L S) (reflectionGroup c t')) ∧
      (∀ n (hn : 0<n) k, k≤n → k≤4 →
        (reflectionPath c t' htfix' htmove' htnorm' n hn i).walk.reverse.getVert k =
          (reflectionPath c t htfix htmove htnorm n hn i).walk.reverse.getVert k) := by
  let A := reducedAmalgam L S
  let a := base (Universal.cosetFamily A) i
  let b := base (Universal.cosetFamily A) (!i)
  have hZR : centerIn J ≤ centralizer (R : Set A.Universal) := by
    intro z hz r hr
    exact hz.2 r (hRJ hr)
  have hZK : centerIn J ≤ centralizer (cartan c : Set A.Universal) := by
    intro z hz k hk
    exact hz.2 k (hKJ hk)
  obtain ⟨z,hz,u,hu,htu,hz2,hu2,huK,hconj⟩ :=
    exists_involution_factor_of_central_product (centerIn J) R (cartan c)
      hZR hZK hdis (t i) htprod (htsq i) (htnorm i)
  have hcomm : Commute z u := ((hZR hz) u hu).symm
  have hagree (v : SourceVertex A) (hv : (sourceGraph A).edist a v≤(3 : ℕ∞)) :
      u • v=t i • v := by
    rw [htu,hcomm.eq,mul_smul,(mem_graphBallFixer _ a 3 z).mp (hball hz) v hv]
  have hufix : u • a=a := (hagree a (by simp)).trans (htfix i)
  have hneigh : u • b=t i • b := by
    apply hagree
    have hab : (sourceGraph A).Adj a b :=
      ⟨by change i≠(!i); cases i <;> decide,incident_base _ _ _⟩
    exact (SimpleGraph.edist_eq_one_iff_adj.mpr hab).le.trans (by norm_num)
  have humove : u • b≠b := by rw [hneigh]; exact htmove i
  let t' : Bool → A.Universal := fun j => if j=i then u else t j
  have he : t' i=u := by simp [t']
  have ho : t' (!i)=t (!i) := by cases i <;> simp [t']
  have hfix' (j : Bool) : t' j • base (Universal.cosetFamily A) j=
      base (Universal.cosetFamily A) j := by
    by_cases hj : j=i
    · subst j; simpa only [he] using hufix
    · simpa only [t',if_neg hj] using htfix j
  have hmove' (j : Bool) : t' j • base (Universal.cosetFamily A) (!j)≠
      base (Universal.cosetFamily A) (!j) := by
    by_cases hj : j=i
    · subst j; simpa only [he] using humove
    · simpa only [t',if_neg hj] using htmove j
  have hsq' (j : Bool) : t' j*t' j=1 := by
    by_cases hj : j=i
    · subst j; simpa only [he] using hu2
    · simpa only [t',if_neg hj] using htsq j
  have hnorm' (j : Bool) : t' j∈normalizer (cartan c : Set A.Universal) := by
    by_cases hj : j=i
    · subst j; simpa only [he] using huK
    · simpa only [t',if_neg hj] using htnorm j
  have hsegment (j : ℤ) (hj : -3≤j ∧ j≤4) :
      alternatingVertex (t' (!i)*t' i) a b j=alternatingVertex (t (!i)*t i) a b j := by
    rw [ho,he]
    exact alternatingVertex_eq_of_agree_three_ball ⟨source_action A⟩
      ⟨by change i≠(!i); cases i <;> decide,incident_base _ _ _⟩
      (htfix i) hufix (htfix (!i)) (htsq i) hu2 (htsq (!i)) hagree j hj
  have hneigh' (j : Bool) : t' j • base (Universal.cosetFamily A) (!j) =
      t j • base (Universal.cosetFamily A) (!j) := by
    by_cases hj : j=i
    · subst j; simpa only [he] using hneigh
    · simp only [t',if_neg hj]
  refine ⟨t',hfix',hmove',hsq',hnorm',he.symm ▸ hu,ho,hneigh',
    ⟨z,hz,by simpa only [he] using htu,hz2⟩,?_,?_,?_⟩
  · simpa only [he] using hconj
  · intro j hlo hhi
    constructor
    · rw [reflectionApartment_eq_oriented_line c t htfix htsq htnorm i]
      exact ⟨j,rfl⟩
    · rw [reflectionApartment_eq_oriented_line c t' hfix' hsq' hnorm' i]
      exact ⟨j,hsegment j ⟨hlo,hhi⟩⟩
  · intro n hn k hkn hk4
    rw [reflectionPath_reverse_getVert c t' hfix' hmove' hsq' hnorm' n hn i k hkn,
      reflectionPath_reverse_getVert c t htfix htmove htsq htnorm n hn i k hkn]
    exact hsegment k (by omega)

include htfix htmove htsq htnorm in
/-- Keeping the other reflection fixes the second path vertex, so the original
vertex-movement condition supplies the branching hypothesis for the new root. -/
theorem source_six_reflection_root_ne_twist_of_unchanged_other
    (h : HypothesisF11 L S)
    (t' : Bool → (reducedAmalgam L S).Universal)
    (htfix' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
      base (Universal.cosetFamily (reducedAmalgam L S)) j)
    (htmove' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
    (htsq' : ∀ j, t' j*t' j=1)
    (htnorm' : ∀ j, t' j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hthick' : ∀ j, ∃ v, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) j) v ∧
      v≠base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ∧
      v≠t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)))
    (i : Bool) (hother : t' (!i)=t (!i))
    (z : (reducedAmalgam L S).Universal) (hz : z∈originalMiddle (reducedAmalgam L S))
    (hzmove : z • (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 ≠
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2) :
    (pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk).map
      (MulAut.conj z).toMonoidHom ≠
        (pathRoots h c 6 (by decide) t' htfix' htmove' htsq' htnorm' htrans hthick' i).root := by
  let p := reflectionPath c t htfix htmove htnorm 6 (by decide) i
  have he : (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk.reverse.getVert 2 =
      p.walk.reverse.getVert 2 := by
    rw [reflectionPath_reverse_getVert c t' htfix' htmove' htsq' htnorm' 6 (by decide) i 2 (by decide),
      reflectionPath_reverse_getVert c t htfix htmove htsq htnorm 6 (by decide) i 2 (by decide)]
    simp only [alternatingVertex,Nat.cast_ofNat,Int.reduceDiv,Int.reduceMod,ite_true,zpow_one,mul_smul,
      htfix,htfix',hother]
  exact source_six_reflection_root_ne_twist h c t' htfix' htmove' htsq' htnorm'
    htrans hthick' hodd p.walk p.isPath p.length_eq p.previous z hz (by rwa [he])

include htfix htmove htsq htnorm in
/-- Original six-path consumer: construct the replacement and exclude the
unwanted Borel conjugates, deriving its thickness from the original marking. -/
theorem source_six_central_reflection_change_with_root_separation
    (h : HypothesisF11 L S) (i : Bool)
    (J R : Subgroup (reducedAmalgam L S).Universal)
    (hRJ : R ≤ J) (hKJ : cartan c ≤ J)
    (hdis : centerIn J ⊓ R=⊥) (htprod : t i∈centerIn J ⊔ R)
    (hball : centerIn J ≤ graphBallFixer (sourceGraph (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 3)
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hthick : ∀ j, ∃ v, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) j) v ∧
      v≠base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ∧
      v≠t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) :
    ∃ (t' : Bool → (reducedAmalgam L S).Universal)
      (htfix' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
        base (Universal.cosetFamily (reducedAmalgam L S)) j)
      (htmove' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
      (_htsq' : ∀ j, t' j*t' j=1)
      (htnorm' : ∀ j, t' j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal)),
      t' i∈R ∧ t' (!i)=t (!i) ∧
      (∃ z∈centerIn J, t i=z*t' i ∧ z*z=1) ∧
      (∀ z∈originalMiddle (reducedAmalgam L S),
        z • (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 ≠
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 →
        (pathRoot (X := (reducedAmalgam L S).Universal)
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk).map
            (MulAut.conj z).toMonoidHom ≠
          pathRoot (X := (reducedAmalgam L S).Universal)
            (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk) := by
  obtain ⟨t',hfix',hmove',hsq',hnorm',hR,hother,hneighbors,hcenter,_hconj,_hsegment,_hpaths⟩ :=
    source_six_central_reflection_change c t htfix htmove htsq htnorm
      i J R hRJ hKJ hdis htprod hball
  have hthick' (j : Bool) : ∃ v, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) j) v ∧
      v≠base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ∧
      v≠t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) := by
    rw [hneighbors j]
    exact hthick j
  refine ⟨t',hfix',hmove',hsq',hnorm',hR,hother,hcenter,?_⟩
  intro z hz hzmove
  exact source_six_reflection_root_ne_twist_of_unchanged_other c t htfix htmove htsq htnorm
    h t' hfix' hmove' hsq' hnorm' htrans hthick' hodd i hother z hz hzmove

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
