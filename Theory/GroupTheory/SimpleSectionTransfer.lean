module
public import Theory.GroupTheory.SimpleSectionNormalAlternative
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Index

/-!
# Removing odd or solvable layers from simple sections

An even-order nonsolvable simple group cannot be a section of an odd-order
or solvable group. A normal odd or solvable kernel can therefore be removed
from any occurrence as a section; if instead the quotient is odd or solvable,
the section already occurs in the normal subgroup.

The normal-image alternative supplies the two possible locations. In the
odd case the surjection and subgroup inclusion contradict order divisibility.
In the solvable case solvability passes to subgroups and images. This is the
layer-removal argument for ABG II.3 Lemma2, article p24. It covers the odd core,
central kernel and odd-index/abelian outer layers without invoking an
odd-order solvability theorem or the later Proposition3 structure theorem.
-/

namespace Subgroup

private theorem no_section_of_odd_or_solvable
    {G T : Type*} [Group G] [Finite G] [Group T]
    (hTtwo : 2 ∣ Nat.card T) (hTns : ¬ Group.IsSolvable T)
    (hG : Odd (Nat.card G) ∨ Group.IsSolvable G)
    (U : Subgroup G) (f : U →* T) (hf : Function.Surjective f) : False := by
  rcases hG with hodd | hsolv
  · exact hodd.not_two_dvd_nat (hTtwo.trans
      ((Subgroup.card_dvd_of_surjective f hf).trans U.card_subgroup_dvd_card))
  · let : Group.IsSolvable G := hsolv
    exact hTns (Group.isSolvable_of_surjective hf)

public theorem simple_section_quotient_of_odd_or_solvable
    {G T : Type*} [Group G] [Finite G] [Group T] [IsSimpleGroup T]
    (hTtwo : 2 ∣ Nat.card T) (hTns : ¬ Group.IsSolvable T)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N) ∨ Group.IsSolvable N)
    (U : Subgroup G) (f : U →* T) (hf : Function.Surjective f) :
    ∃ W : Subgroup (G ⧸ N), ∃ g : W →* T, Function.Surjective g := by
  rcases simple_section_normal_or_quotient N U f hf with ⟨W, g, hg⟩ | h
  · exact False.elim (no_section_of_odd_or_solvable hTtwo hTns hN W g hg)
  · exact h

public theorem simple_section_normal_of_quotient_odd_or_solvable
    {G T : Type*} [Group G] [Finite G] [Group T] [IsSimpleGroup T]
    (hTtwo : 2 ∣ Nat.card T) (hTns : ¬ Group.IsSolvable T)
    (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card (G ⧸ N)) ∨ Group.IsSolvable (G ⧸ N))
    (U : Subgroup G) (f : U →* T) (hf : Function.Surjective f) :
    ∃ W : Subgroup N, ∃ g : W →* T, Function.Surjective g := by
  rcases simple_section_normal_or_quotient N U f hf with h | ⟨W, g, hg⟩
  · exact h
  · exact False.elim (no_section_of_odd_or_solvable hTtwo hTns hN W g hg)

end Subgroup
