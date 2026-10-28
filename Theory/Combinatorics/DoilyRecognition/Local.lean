module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Data.Finset.Card

/-!
# Local coordinates for the doily

A triangle in the strongly regular graph with parameters (15,6,1,3) has three disjoint outside-neighbor blocks of size four. Each block is a perfect matching. These are the local source coordinates for Aschbacher (1994), p249, Exercise2(3).
-/

@[expose] public section

open Finset
namespace Theory.Combinatorics.Doily
variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable (G:SimpleGraph Ω) [DecidableRel G.Adj]

structure Triangle where
  point : Fin 3→Ω
  injective : Function.Injective point
  adjacent : ∀i j,i≠j→G.Adj (point i) (point j)

namespace Triangle
variable {G} (t:Triangle G)
def block (i:Fin 3) : Finset Ω :=
  (G.neighborFinset (t.point i)) \ Finset.univ.image t.point

theorem mem_block {i:Fin 3} {x:Ω} :
    x∈t.block i ↔ G.Adj (t.point i) x ∧ ∀j,x≠t.point j := by
  simp only [block,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,Finset.mem_image,
    Finset.mem_univ,true_and,not_exists]
  constructor
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun j hh=>hn j hh.symm⟩
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun j hh=>hn j hh.symm⟩
end Triangle

variable {G}
omit [DecidableEq Ω] in
 theorem common_eq (h:G.IsSRGWith 15 6 1 3) {x y a b:Ω}
    (hxy:G.Adj x y) (hxa:G.Adj x a) (hya:G.Adj y a)
    (hxb:G.Adj x b) (hyb:G.Adj y b) : a=b := by
  have hc:=h.of_adj x y hxy
  obtain ⟨u,hu⟩:=Fintype.card_eq_one_iff.mp hc
  exact congrArg Subtype.val ((hu ⟨a,hxa,hya⟩).trans (hu ⟨b,hxb,hyb⟩).symm)

omit [DecidableEq Ω] in
 theorem exists_triangle (h:G.IsSRGWith 15 6 1 3) : Nonempty (Triangle G) := by
  have hn:Nonempty Ω:=Fintype.card_pos_iff.mp (by rw [h.card];decide)
  obtain ⟨x⟩:=hn
  have hc:Fintype.card (G.neighborSet x)=6:=by rw [G.card_neighborSet_eq_degree,h.regular.degree_eq]
  obtain ⟨y,hy⟩:Nonempty (G.neighborSet x):=Fintype.card_pos_iff.mp (by rw [hc];decide)
  have hxy:G.Adj x y:=hy
  have ha:=h.of_adj x y hxy
  obtain ⟨z,hz⟩:Nonempty (G.commonNeighbors x y):=Fintype.card_pos_iff.mp (by rw [ha];decide)
  refine ⟨⟨![x,y,z],?_,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hxy.ne hij).elim
    · exact (hz.1.ne hij).elim
    · exact (hxy.ne hij.symm).elim
    · rfl
    · exact (hz.2.ne hij).elim
    · exact (hz.1.ne hij.symm).elim
    · exact (hz.2.ne hij.symm).elim
    · rfl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hxy
    · exact hz.1
    · exact hxy.symm
    · exact (hij rfl).elim
    · exact hz.2
    · exact hz.1.symm
    · exact hz.2.symm
    · exact (hij rfl).elim


namespace Triangle
variable (t:Triangle G) (h:G.IsSRGWith 15 6 1 3)
include h
 theorem block_card (i:Fin 3) : (t.block i).card=4 := by
  have hi:Finset.univ.image t.point ∩ G.neighborFinset (t.point i)=
      (Finset.univ.erase i).image t.point := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_image,Finset.mem_univ,true_and,
      SimpleGraph.mem_neighborFinset,Finset.mem_erase]
    constructor
    · rintro ⟨⟨j,rfl⟩,hj⟩
      exact ⟨j,⟨(fun hh=>hj.ne (congrArg t.point hh.symm)),trivial⟩,rfl⟩
    · rintro ⟨j,⟨hj,_⟩,rfl⟩
      exact ⟨⟨j,rfl⟩,t.adjacent i j hj.symm⟩
  rw [block,Finset.card_sdiff,hi,Finset.card_image_of_injective _ t.injective,
    Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,
    G.card_neighborFinset_eq_degree,h.regular.degree_eq]

 theorem block_disjoint {i j:Fin 3} (hij:i≠j) : Disjoint (t.block i) (t.block j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨k,hki,hkj⟩:∃k:Fin 3,k≠i∧k≠j:=by
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | (decide +kernel)
  have he:=common_eq h (t.adjacent i j hij)
    (t.mem_block.mp hxi).1 (t.mem_block.mp hxj).1
    (t.adjacent i k hki.symm) (t.adjacent j k hkj.symm)
  exact (t.mem_block.mp hxi).2 k he

 theorem block_matching (i:Fin 3) (x:Ω) (hx:x∈t.block i) :
    ∃!y:Ω,y∈t.block i ∧ G.Adj x y := by
  have hx':=t.mem_block.mp hx
  have hc:=h.of_adj (t.point i) x hx'.1
  obtain ⟨y,hy⟩:Nonempty (G.commonNeighbors (t.point i) x):=
    Fintype.card_pos_iff.mp (by rw [hc];decide)
  have hyb:y∈t.block i:=by
    apply t.mem_block.mpr
    refine ⟨hy.1,?_⟩
    intro j hej
    by_cases hji:j=i
    · subst j
      exact hy.1.ne hej.symm
    · have hxj:x∈t.block j:=t.mem_block.mpr ⟨hej ▸ hy.2.symm,hx'.2⟩
      exact Finset.disjoint_left.mp (t.block_disjoint h (fun hh=>hji hh.symm)) hx hxj

  refine ⟨y,⟨hyb,hy.2⟩,?_⟩
  intro z hz
  exact common_eq h hx'.1 (t.mem_block.mp hz.1).1 hz.2 hy.1 hy.2
end Triangle
end Theory.Combinatorics.Doily
