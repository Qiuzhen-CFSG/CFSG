module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceRootRegularity
public import Theory.GroupTheory.WeakBNPair.RegularTree.BranchingPathFixers

/-!
# Separation of the original six-path roots after a reflection change

In the nonbinary part of DGS (14.17), the new apartment shares its initial
segment with the old one. The unwanted complement would be a conjugate
of the old six-path root by an element fixing the first neighbor and moving
the second vertex. The two five-edge tails then form a ten-edge simple
path. Odd seven-path stabilizers force the intersection of the two roots
to be trivial.

The application to a constructed reflection path rules out equality with
that conjugate: thickness and seven-path transitivity already supply a
nonidentity element in its actual path radical. All roots here are the
literal two-cores of path fixers in the original universal completion,
and the conjugating element belongs to the original whole Borel.

This proves the geometric exclusion on printed p.222. Constructing the
r=6 local quotient module, its two-complement classification and the
compatible changed reflection remains necessary for full (14.17). The
binary case, other Chapter 14 branches and the exceptional alternative of
(14.19) are not discharged by this exclusion.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(14.17), printed pp.221--223, especially p.222.
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

/-- The unwanted conjugate complement in (14.17) meets the new six-path
radical trivially, on the original universal tree and with its actual Borel. -/
theorem source_six_path_twisted_root_disjoint
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)))
    {i : Bool} {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (q : (sourceGraph (reducedAmalgam L S)).Walk b
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (hp : p.IsPath) (hq : q.IsPath) (hpl : p.length=6) (hql : q.length=6)
    (hprev : p.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hqprev : q.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (z : (reducedAmalgam L S).Universal) (hz : z∈originalMiddle (reducedAmalgam L S))
    (hbranch : z • p.reverse.getVert 2 ≠ q.reverse.getVert 2) :
    (pathRoot (X := (reducedAmalgam L S).Universal) p).map
      (MulAut.conj z).toMonoidHom ⊓ pathRoot q=⊥ := by
  let A := reducedAmalgam L S
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 1)
  have hzfix : z • base (Universal.cosetFamily A) (!i) = base (Universal.cosetFamily A) (!i) := by
    change z∈MulAction.stabilizer A.Universal (base (Universal.cosetFamily A) (!i))
    rw [stabilizer_base]
    have hzo : z∈(Universal.left A).range ⊓ (Universal.right A).range := by
      rw [Universal.overlap_eq A hL hR]
      exact hz
    cases i
    · exact hzo.2
    · exact hzo.1
  have hz1 : z • p.reverse.getVert 1=q.reverse.getVert 1 := by
    rw [SimpleGraph.Walk.getVert_reverse,SimpleGraph.Walk.getVert_reverse]
    change z • p.penultimate=q.penultimate
    rw [hprev,hqprev]
    exact hzfix
  have he := conjugate_pathRoot_inf_eq_bot_of_branch
    (Universal.cosetGraph_isTree A hL hR) (source_action A) 7 hodd
    p.reverse q.reverse hp.reverse hq.reverse
    (by simp only [SimpleGraph.Walk.length_reverse,hpl]; decide)
    (by simp only [SimpleGraph.Walk.length_reverse,hql]; decide)
    (by simp only [SimpleGraph.Walk.length_reverse,hpl,hql]; decide) z hz1 hbranch
  simpa only [pathRoot_reverse] using he

variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
  base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (htsq : ∀ i, t i * t i = 1)
variable (htnorm : ∀ i, t i ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) 7)
variable (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
  (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
  z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
  z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
  p.IsPath → p.length=7 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)))

include hodd in
/-- The genuine root constructed from the changed reflections cannot be the
unwanted conjugate of the original root. Its nontriviality is proved from
the source path action and thickness, rather than supplied as a premise. -/
theorem source_six_reflection_root_ne_twist
    {i : Bool} {a : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (hp : p.IsPath) (hpl : p.length=6)
    (hprev : p.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (z : (reducedAmalgam L S).Universal) (hz : z∈originalMiddle (reducedAmalgam L S))
    (hbranch : z • p.reverse.getVert 2 ≠
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2) :
    (pathRoot (X := (reducedAmalgam L S).Universal) p).map (MulAut.conj z).toMonoidHom ≠
      (pathRoots h c 6 (by decide) t htfix htmove htsq htnorm htrans hthick i).root := by
  let q := reflectionPath c t htfix htmove htnorm 6 (by decide) i
  have he := source_six_path_twisted_root_disjoint hodd p q.walk hp q.isPath
    hpl q.length_eq hprev q.previous z hz hbranch
  intro hEq
  have hEq' : (pathRoot (X := (reducedAmalgam L S).Universal) p).map
      (MulAut.conj z).toMonoidHom=pathRoot q.walk := hEq
  rw [hEq',inf_idem] at he
  obtain ⟨x,hx,hxo⟩ := pathRoots_exists_involution h c 6 (by decide)
    t htfix htmove htsq htnorm htrans hthick i
  have hx' : x∈pathRoot (X := (reducedAmalgam L S).Universal) q.walk := hx
  rw [he] at hx'
  have hxo' : orderOf x=1 := orderOf_eq_one_iff.mpr hx'
  omega

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
