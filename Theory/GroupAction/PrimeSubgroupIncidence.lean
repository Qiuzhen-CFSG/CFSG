module

public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Incidence through commuting prime-order subgroups

Two distinct overgroups are incident when they contain commuting
prime-order subgroups invariant under one fixed marked subgroup.
Conjugation by its normalizer preserves all the original witnesses,
including their containment and centralizer relations.

Source application: the repaired parabolic graph in Aschbacher--Smith
J.4.10, printed p.444, with prime five and the original four-group span.
-/

public section
noncomputable section
namespace Subgroup.PrimeIncidence
open Subgroup
variable {G:Type*} [Group G]

/-- Distinct overgroups are adjacent if they contain commuting order-p
subgroups normalized by the same marked subgroup V. -/
def graph (p:ℕ) (V:Subgroup G) : SimpleGraph (Subgroup G) where
  Adj E F := E≠F ∧ ∃ A B:Subgroup G,A≤E ∧ B≤F ∧ Nat.card A=p ∧ Nat.card B=p ∧
    V≤normalizer (A:Set G) ∧ V≤normalizer (B:Set G) ∧ A≤centralizer (B:Set G)
  symm := ⟨by
    rintro E F ⟨hne,A,B,hAE,hBF,hA,hB,hVA,hVB,hc⟩
    refine ⟨hne.symm,B,A,hBF,hAE,hB,hA,hVB,hVA,?_⟩
    intro b hb a ha
    exact (hc ha b hb).symm⟩
  loopless := ⟨by
    intro E h
    exact h.1 rfl⟩

theorem adj_iff (p:ℕ) (V E F:Subgroup G) : (graph p V).Adj E F ↔
    E≠F ∧ ∃ A B:Subgroup G,A≤E ∧ B≤F ∧ Nat.card A=p ∧ Nat.card B=p ∧
      V≤normalizer (A:Set G) ∧ V≤normalizer (B:Set G) ∧ A≤centralizer (B:Set G) := Iff.rfl

theorem conj_adj {p:ℕ} {V E F:Subgroup G} (g:G) (hg:g∈normalizer (V:Set G))
    (h:(graph p V).Adj E F) : (graph p V).Adj (E.conjBy g) (F.conjBy g) := by
  obtain ⟨hne,A,B,hAE,hBF,hA,hB,hVA,hVB,hc⟩:=h
  have hV:V.map (MulAut.conj g).toMonoidHom=V:=mem_normalizer_iff_map_conj_eq.mp hg
  have hn (A:Subgroup G) (hVA:V≤normalizer (A:Set G)) :
      V≤normalizer (A.conjBy g:Set G) := by
    have hh := (map_mono (f:=(MulAut.conj g).toMonoidHom) hVA).trans
      (A.le_normalizer_map (MulAut.conj g).toMonoidHom)
    rwa [hV] at hh
  refine ⟨fun he=>hne (map_injective (MulAut.conj g).injective he),A.conjBy g,B.conjBy g,
    map_mono hAE,map_mono hBF,?_,?_,hn A hVA,hn B hVB,?_⟩
  · exact (card_map_of_injective (MulAut.conj g).injective).trans hA
  · exact (card_map_of_injective (MulAut.conj g).injective).trans hB
  · rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) (hc ha b hb)

theorem conj_adj_iff {p:ℕ} {V E F:Subgroup G} (g:G) (hg:g∈normalizer (V:Set G)) :
    (graph p V).Adj (E.conjBy g) (F.conjBy g) ↔ (graph p V).Adj E F := by
  refine ⟨fun h=>?_,conj_adj g hg⟩
  have hh:=conj_adj g⁻¹ (inv_mem hg) h
  simpa only [conjBy_inv] using hh
end Subgroup.PrimeIncidence
