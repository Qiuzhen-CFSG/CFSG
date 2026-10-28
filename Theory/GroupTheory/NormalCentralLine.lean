module
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.AbelianIndexTwoCentralizers

/-!
# A normal subgroup detected by its central involution

In a finite two-group, a nontrivial normal subgroup meets the center.
When a normal subgroup X meets that center in one involution line, any
other normal subgroup D missing the involution is disjoint from X and
therefore centralizes X. Faithful nonabelian images of D and X cannot
both lie in a group with an abelian subgroup of index two.

This gives the marked involution step for the dihedral and semidihedral
source automizers in Aschbacher--Smith 2.5.21, printed p.566.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normal intersection is trivial when it misses the unique central involution. -/
theorem disjoint_of_misses_normal_central_line
    (S D X : Subgroup G) (hS : IsPGroup 2 S)
    (hDS : D ≤ S) (hXS : X ≤ S)
    (hDn : S ≤ normalizer (D : Set G)) (hXn : S ≤ normalizer (X : Set G))
    (t : G) (ht : orderOf t = 2) (hline : centerIn S ⊓ X = zpowers t)
    (htD : t ∉ D) : Disjoint D X := by
  apply disjoint_iff.mpr
  by_contra hn
  have hc := inf_centerIn_ne_bot hS hn ((inf_le_inf hDS hXS).trans inf_le_left)
    ((le_inf hDn hXn).trans inf_normalizer_le_normalizer_inf)
  apply hc
  apply bot_unique
  intro a ha
  have ham : a ∈ zpowers t := hline ▸ ⟨ha.2, ha.1.2⟩
  by_contra ha1
  have he : a = t := by
    have hcard : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
    obtain ⟨_, _, hz⟩ := (Nat.card_eq_two_iff' (1 : zpowers t)).mp hcard
    have ht1 : (⟨t, mem_zpowers t⟩ : zpowers t) ≠ 1 := by
      intro h; have hh := congrArg Subtype.val h; change t = 1 at hh
      rw [hh, orderOf_one] at ht; omega
    have ha1' : (⟨a, ham⟩ : zpowers t) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    exact congrArg Subtype.val ((hz _ ha1').trans (hz _ ht1).symm)
  exact htD (he ▸ ha.1.1)

omit [Finite G] in
/-- Disjoint relatively normal subgroups centralize one another. -/
theorem centralizes_of_disjoint_normal_in
    (S D X : Subgroup G) (hDS : D ≤ S) (hXS : X ≤ S)
    (hDn : S ≤ normalizer (D : Set G)) (hXn : S ≤ normalizer (X : Set G))
    (hd : Disjoint D X) : X ≤ centralizer (D : Set G) := by
  let D' := D.subgroupOf S
  let X' := X.subgroupOf S
  let : D'.Normal := normal_subgroupOf_of_le_normalizer hDn
  let : X'.Normal := normal_subgroupOf_of_le_normalizer hXn
  have hd' : Disjoint X' D' := by
    apply disjoint_def.mpr
    intro a haX haD
    exact Subtype.ext (disjoint_def.mp hd haD haX)
  have hc : X' ≤ centralizer (D' : Set S) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique ((commutator_le_inf X' D').trans (disjoint_iff.mp hd').le))
  intro a ha b hb
  exact congrArg Subtype.val (hc (show (⟨a, hXS ha⟩ : S) ∈ X' from ha) ⟨b, hDS hb⟩ hb)
/-- Faithful commuting images in an abelian-index-two group force the marked
central involution of X into D. -/
theorem central_line_mem_of_faithful_nonabelian_images
    {Q : Type*} [Group Q]
    (S D X : Subgroup G) (hS : IsPGroup 2 S)
    (hDS : D ≤ S) (hXS : X ≤ S)
    (hDn : S ≤ normalizer (D : Set G)) (hXn : S ≤ normalizer (X : Set G))
    (t : G) (ht : orderOf t = 2) (hline : centerIn S ⊓ X = zpowers t)
    (f : S →* Q)
    (hfD : Function.Injective (f.comp (inclusion hDS)))
    (hfX : Function.Injective (f.comp (inclusion hXS)))
    (hnD : ¬ IsMulCommutative D) (hnX : ¬ IsMulCommutative X)
    (A : Subgroup Q) [IsMulCommutative A] (hi : A.index = 2) : t ∈ D := by
  by_contra htD
  have hd := disjoint_of_misses_normal_central_line S D X hS hDS hXS hDn hXn t ht hline htD
  have hc := centralizes_of_disjoint_normal_in S D X hDS hXS hDn hXn hd
  apply not_nonabelian_commuting_images_of_abelian_index_two A hi
    (f.comp (inclusion hDS)) hfD (f.comp (inclusion hXS)) hfX hnD hnX
  intro d x
  have hh : (⟨d, hDS d.property⟩ : S) * ⟨x, hXS x.property⟩ =
      ⟨x, hXS x.property⟩ * (⟨d, hDS d.property⟩ : S) :=
    Subtype.ext (hc x.property d d.property)
  change f ⟨d, hDS d.property⟩ * f ⟨x, hXS x.property⟩ =
    f ⟨x, hXS x.property⟩ * f ⟨d, hDS d.property⟩
  simpa only [map_mul] using congrArg f hh

end Subgroup
