module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReflectionPaths
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Transport between the actual oriented path radicals

Extend two equally long paths ending at the original oriented edge by one
vertex and use rooted path transitivity. The resulting transporter fixes
both marked endpoints, so lies in the full Borel. If the Cartan fixes the
first path, the factorization B = UK removes its Cartan factor. Thus the
actual Borel two-group U conjugates the two path radicals.

This comparison requires the literal path length, preceding vertex and
Cartan fixation; an arbitrary path supplied with a reflection need not have
these properties. Source: DGS, *Groups and Graphs* (1985), (14.1)--(14.2),
printed pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

include h in
/-- Matching oriented source paths can be transported by the actual Borel two-group. -/
theorem exists_twoGroup_pathRoot_transport
    (n : ℕ) (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) (n+1))
    (hthick : ∀ v a b : SourceVertex (reducedAmalgam L S), ∃ z,
      (sourceGraph (reducedAmalgam L S)).Adj v z ∧ z≠a ∧ z≠b)
    {i : Bool} {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (q : (sourceGraph (reducedAmalgam L S)).Walk b (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (hp : p.IsPath) (hq : q.IsPath) (hpn : p.length=n) (hqn : q.length=n)
    (hprev : p.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hqprev : q.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hK : cartan c≤pathFixer (X := (reducedAmalgam L S).Universal) p) :
    ∃ u∈twoGroup L S, (pathRoot (X := (reducedAmalgam L S).Universal) p).map
      (MulAut.conj u).toMonoidHom = pathRoot q := by
  let A := reducedAmalgam L S
  have hac := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  obtain ⟨v,hv,hvne,_⟩ := hthick a p.reverse.penultimate p.reverse.penultimate
  obtain ⟨w,hw,hwne,_⟩ := hthick b q.reverse.penultimate q.reverse.penultimate
  have hvnew : v∉p.reverse.support := fun hm => hvne (hac.eq_penultimate_of_adj_end hp.reverse hv hm)
  have hwnew : w∉q.reverse.support := fun hm => hwne (hac.eq_penultimate_of_adj_end hq.reverse hw hm)
  obtain ⟨g,hg⟩ := htrans (p.reverse.concat hv) (q.reverse.concat hw)
    (hp.reverse.concat hvnew hv) (hq.reverse.concat hwnew hw)
    (by simp only [SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_reverse,hpn])
    (by simp only [SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_reverse,hqn])
  have hg' (k : ℕ) (hk : k≤n) : g • p.getVert k=q.getVert k := by
    have he := hg (n-k) (by omega)
    have hle₁ : n-k≤p.reverse.length := by simpa only [SimpleGraph.Walk.length_reverse,hpn] using (Nat.sub_le n k)
    have hle₂ : n-k≤q.reverse.length := by simpa only [SimpleGraph.Walk.length_reverse,hqn] using (Nat.sub_le n k)
    simpa only [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append',
      if_pos hle₁,if_pos hle₂,SimpleGraph.Walk.getVert_reverse,hpn,hqn,
      Nat.sub_sub_self hk] using he
  have hge : g∈Universal.cosetFamily A i := by
    rw [←stabilizer_base (F := Universal.cosetFamily A) (i := i)]
    have he := hg' n le_rfl
    rw [←hpn,SimpleGraph.Walk.getVert_length] at he
    rw [hpn,←hqn,SimpleGraph.Walk.getVert_length] at he
    exact he
  have hgf : g∈Universal.cosetFamily A (!i) := by
    rw [←stabilizer_base (F := Universal.cosetFamily A) (i := !i)]
    have he := hg' (n-1) (Nat.sub_le _ _)
    change g • p.getVert (n-1)=q.getVert (n-1) at he
    have hpv : p.getVert (n-1)=p.penultimate := by rw [←hpn]
    have hqv : q.getVert (n-1)=q.penultimate := by rw [←hqn]
    rw [hpv,hqv,hprev,hqprev] at he
    exact he
  have hgB : g∈originalMiddle A := by
    rw [originalMiddle,←Universal.overlap_eq A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))]
    cases i
    · exact ⟨hge,hgf⟩
    · exact ⟨hgf,hge⟩
  have hgprod : g∈(twoGroup L S : Set A.Universal)*(cartan c : Set A.Universal) := by
    rw [←factorization_set h c]
    exact hgB
  obtain ⟨u,hu,k,hk,rfl⟩ := hgprod
  refine ⟨u,hu,pathRoot_map_conj p q u (hpn.trans hqn.symm) ?_⟩
  intro j hj
  have he := hg' j (by omega)
  simpa only [mul_smul,hK hk j hj] using he


end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
