module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto


/-!
# Cliques of adjacent subspaces

Equal-dimensional subspaces whose pairwise intersections have codimension
at most one form either a common-hyperplane family or a family contained
in one common over-space. The proof compares three members by the dimension
formula, then excludes simultaneous members of the two different kinds.
This is the Grassmann-clique argument used in the binary orbit form of
Meierfrankenfeld--Stellmacher (1993), (1.6), printed pp.845--847.
-/

public section
open Module
namespace Submodule
variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

lemma rank_intersection_of_adjacent {U V' : Submodule k V} {n : ℕ}
    (hU : finrank k U=n) (hV : finrank k V'=n)
    (hUV : n ≤ finrank k ↥(U⊓V')+1) (hne : U≠V') :
    finrank k ↥(U⊓V')+1=n := by
  have hlt : U⊓V' < U := lt_of_le_of_ne inf_le_left (by
    intro h
    have hle : U≤V' := h ▸ inf_le_right
    exact hne (eq_of_le_of_finrank_eq hle (hU.trans hV.symm)))
  have hh := finrank_lt_finrank_of_lt hlt
  omega

lemma adjacent_third {U V' W : Submodule k V} {n : ℕ}
    (hU : finrank k U=n) (hV : finrank k V'=n) (hW : finrank k W=n)
    (hUV : n ≤ finrank k ↥(U⊓V')+1) (hneq : U≠V')
    (hUW : n ≤ finrank k ↥(U⊓W)+1)
    (hVW : n ≤ finrank k ↥(V'⊓W)+1) :
    U⊓V'≤W ∨ W≤U⊔V' := by
  by_cases hA : U⊓V'≤W
  · exact Or.inl hA
  right
  by_cases he : U=W
  · exact he ▸ le_sup_left
  by_cases he' : V'=W
  · exact he' ▸ le_sup_right
  have hX := rank_intersection_of_adjacent hU hW hUW he
  have hY := rank_intersection_of_adjacent hV hW hVW he'
  have hlt : U⊓V'⊓W < U⊓V' := lt_of_le_of_ne inf_le_left (by
    intro heq
    exact hA (heq ▸ inf_le_right))
  have hd := finrank_lt_finrank_of_lt hlt
  have hAb := rank_intersection_of_adjacent hU hV hUV hneq
  have hsum := finrank_sup_add_finrank_inf_eq (U⊓W) (V'⊓W)
  have heq : (U⊓W)⊓(V'⊓W)=U⊓V'⊓W := by
    ext x
    simp only [mem_inf]
    tauto
  rw [heq] at hsum
  have hle : (U⊓W)⊔(V'⊓W)≤W := sup_le inf_le_right inf_le_right
  have hWB := eq_of_le_of_finrank_eq hle (by
    have hdim := finrank_mono hle
    omega)
  rw [← hWB]
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

lemma clique_star_or_top {ι : Type*} (W : ι → Submodule k V) (n : ℕ)
    (hr : ∀ i, finrank k ↥(W i)=n)
    (ha : ∀ i j, n ≤ finrank k ↥(W i⊓W j)+1)
    (i j : ι) (hne : W i≠W j) :
    (∀ l, W i⊓W j≤W l) ∨ (∀ l, W l≤W i⊔W j) := by
  by_cases htop : ∀ l, W l≤W i⊔W j
  · exact Or.inr htop
  push Not at htop
  obtain ⟨l,hl⟩ := htop
  have hlA := (adjacent_third (hr i) (hr j) (hr l) (ha i j) hne (ha i l) (ha j l)).resolve_right hl
  left
  intro m
  by_contra hm
  have hmB := (adjacent_third (hr i) (hr j) (hr m) (ha i j) hne (ha i m) (ha j m)).resolve_left hm
  have hAr := rank_intersection_of_adjacent (hr i) (hr j) (ha i j) hne
  have hBl : W l⊓(W i⊔W j)=W i⊓W j := by
    have hlt : W l⊓(W i⊔W j)<W l := lt_of_le_of_ne inf_le_left (by
      intro heq
      exact hl (heq ▸ inf_le_right))
    have hd := finrank_lt_finrank_of_lt hlt
    have hle : W i⊓W j≤W l⊓(W i⊔W j) := le_inf hlA (inf_le_left.trans le_sup_left)
    exact (eq_of_le_of_finrank_eq hle (by
      have hdim := finrank_mono hle
      have hh := hr l
      omega)).symm
  have hlt : W i⊓W j⊓W m<W i⊓W j := lt_of_le_of_ne inf_le_left (by
    intro heq
    exact hm (heq ▸ inf_le_right))
  have hd := finrank_lt_finrank_of_lt hlt
  have hle : W l⊓W m≤W i⊓W j⊓W m := by
    apply le_inf _ inf_le_right
    rw [← hBl]
    exact le_inf inf_le_left (inf_le_right.trans hmB)
  have hdim := finrank_mono hle
  have hadj := ha l m
  omega

lemma clique_intersection_or_span_rank {ι : Type*} (W : ι → Submodule k V) (n : ℕ)
    (hr : ∀ i, finrank k (W i)=n)
    (ha : ∀ i j, n ≤ finrank k ↥(W i⊓W j)+1)
    (i j : ι) (hne : W i≠W j) :
    finrank k ↥(⨅ l, W l)+1=n ∨ finrank k ↥(⨆ l, W l)=n+1 := by
  have hA := rank_intersection_of_adjacent (hr i) (hr j) (ha i j) hne
  rcases clique_star_or_top W n hr ha i j hne with hs | ht
  · left
    have he : (⨅ l, W l)=W i⊓W j :=
      le_antisymm (le_inf (iInf_le W i) (iInf_le W j)) (le_iInf hs)
    rw [he]
    exact hA
  · right
    have he : (⨆ l, W l)=W i⊔W j :=
      le_antisymm (iSup_le ht) (sup_le (le_iSup W i) (le_iSup W j))
    rw [he]
    have hh := finrank_sup_add_finrank_inf_eq (W i) (W j)
    rw [hr i,hr j] at hh
    omega

end Submodule
