module
public import Theory.GroupAction.NormalizerFrattini
public import Theory.GroupTheory.Commutator.Basic

/-!
# Normal intersections of irreducible Frattini actors

An ambient normal subgroup meets an irreducible Frattini actor either in
its Frattini subgroup or in the whole actor. Applied to a normal component
and its centralizer, this gives the two exact intersection alternatives
used after the inner-action step of intrinsic containment.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.510.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsNormalizerFrattiniIrreducible.inf_normal_le_frattini_or_le
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    (N : Subgroup G) [N.Normal] :
    P ⊓ N ≤ (frattini P).map P.subtype ∨ P ≤ N := by
  rcases hirr.invariant_le_frattini_or_eq (N.subgroupOf P)
    (fun s d hd => (inferInstance : N.Normal).conj_mem d hd s) with hf | ht
  · left
    rintro x ⟨hxP, hxN⟩
    exact mem_map_of_mem P.subtype (hf (show (⟨x, hxP⟩ : P) ∈ N.subgroupOf P from hxN))
  · right
    intro x hxP
    have hx : (⟨x, hxP⟩ : P) ∈ N.subgroupOf P := ht.symm ▸ mem_top _
    exact hx

theorem IsNormalizerFrattiniIrreducible.centralizer_le_frattini
    {P N : Subgroup G} [N.Normal] (hirr : IsNormalizerFrattiniIrreducible P)
    (hn : ⁅N,P⁆ ≠ ⊥) :
    P ⊓ centralizer (N : Set G) ≤ (frattini P).map P.subtype := by
  rcases hirr.inf_normal_le_frattini_or_le (centralizer (N : Set G)) with hf | hc
  · exact hf
  · exact (hn (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))).elim

end Subgroup
