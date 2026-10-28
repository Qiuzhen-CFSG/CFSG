module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathReflectionChange
public import Theory.GroupTheory.CentralInvolutionProjectionGeneration

/-!
# Identifying the root after the central reflection change

The two-complement conclusion in DGS (14.17) says that the new six-path
root is the old root or one of its specified Borel conjugates. The genuine
path-root separation theorem excludes the latter alternative. Projection
off the central factor then shows that the new root and reflection generate
the same complementary group, so its trivial two-core is retained.

This module completes that conditional step on the literal universal tree.
The original local profiles must still supply the central splitting,
radius-three fixation, two-complement alternatives and trivial two-core of
the complementary rank-one group. It does not assert full exchange from
those still-undischarged source hypotheses.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(14.16)--(14.17), printed pp.220--222.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (c : CompatibleCartans L (reducedSylow L S))
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
  base (Universal.cosetFamily (reducedAmalgam L S)) j)
variable (htmove : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
variable (htsq : ∀ j, t j*t j=1)
variable (htnorm : ∀ j, t j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

/-- The precise local complement-classification input: every compatible
replacement retaining the four-vertex prefix has either the original root
or a Borel twist moving its second vertex. The invariant-module producer
must prove this assertion from the original local quotient. -/
structure SixPathReplacementAlternatives (i : Bool)
    (R : Subgroup (reducedAmalgam L S).Universal) : Prop where
  alternatives : ∀
    (t' : Bool → (reducedAmalgam L S).Universal)
    (htfix' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
      base (Universal.cosetFamily (reducedAmalgam L S)) j)
    (htmove' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
    (_htsq' : ∀ j, t' j*t' j=1)
    (htnorm' : ∀ j, t' j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal)),
    t' i∈R → t' (!i)=t (!i) →
    (∀ k, k≤4 →
      (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk.reverse.getVert k =
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert k) →
    pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk =
      pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk ∨
    ∃ z∈originalMiddle (reducedAmalgam L S),
      z • (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 ≠
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 ∧
      pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk =
      (pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk).map
          (MulAut.conj z).toMonoidHom

include htfix htmove htsq htnorm in
/-- The actual changed six-path has exactly the original root. Together
with the projected reflection it generates the original rank-one factor,
whose trivial two-core supplies the local conclusion on DGS p.222. -/
theorem source_six_central_replacement_root
    (h : HypothesisF11 L S) (i : Bool)
    (J R : Subgroup (reducedAmalgam L S).Universal)
    (hRJ : R ≤ J) (hKJ : cartan c ≤ J)
    (hdis : centerIn J ⊓ R=⊥) (htprod : t i∈centerIn J ⊔ R)
    (hball : centerIn J ≤ graphBallFixer (sourceGraph (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 3)
    (hroot : pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk ≤ R)
    (hgen : R ≤ pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk ⊔ zpowers (t i))
    (hcore : pCore 2 R=⊥)
    (hchoices : SixPathReplacementAlternatives c t htfix htmove htnorm i R)
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
      pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk =
        pathRoot (X := (reducedAmalgam L S).Universal)
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk ∧
      pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk ⊔
          zpowers (t' i) = R ∧
      pCore 2 (pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk ⊔
          zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal)=⊥ := by
  obtain ⟨t',hfix',hmove',hsq',hnorm',hR,hother,hneighbors,hcenter,_hconj,_hsegment,hpaths⟩ :=
    source_six_central_reflection_change c t htfix htmove htsq htnorm
      i J R hRJ hKJ hdis htprod hball
  have hthick' (j : Bool) : ∃ v, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) j) v ∧
      v≠base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ∧
      v≠t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) := by
    rw [hneighbors j]
    exact hthick j
  have heq : pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t' hfix' hmove' hnorm' 6 (by decide) i).walk =
      pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk := by
    rcases hchoices.alternatives t' hfix' hmove' hsq' hnorm' hR hother
        (fun k hk => hpaths 6 (by decide) k (by omega) hk) with heq | ⟨z,hz,hmove,heq⟩
    · exact heq
    · exact (source_six_reflection_root_ne_twist_of_unchanged_other c t htfix htmove
        htsq htnorm h t' hfix' hmove' hsq' hnorm' htrans hthick' hodd
        i hother z hz hmove heq.symm).elim
  have hgen' : pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t' hfix' hmove' hnorm' 6 (by decide) i).walk ⊔
        zpowers (t' i) = R := by
    rw [heq]
    obtain ⟨z,hz,htz,_hz2⟩ := hcenter
    exact sup_zpowers_eq_of_central_factor (centerIn J) R _
      (fun z hz r hr => hz.2 r (hRJ hr)) hdis hroot
      (t i) z (t' i) hz hR htz hgen
  refine ⟨t',hfix',hmove',hsq',hnorm',hR,hother,hcenter,heq,hgen',?_⟩
  rw [hgen']
  exact hcore

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
