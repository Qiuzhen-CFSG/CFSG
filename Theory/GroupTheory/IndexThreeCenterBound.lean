module
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Mathlib.Tactic

/-!
# Center bounds from two conjugate index-three subgroups

A nonnormal index-three subgroup and a suitable conjugate generate the group.
If an abelian normal subgroup Q contains a half-sized subgroup Z centralized by
that index-three subgroup, then Z intersected with the corresponding conjugate
lies in the whole center. The subgroup product formula yields |Q:Z(G)| ≤ 4
in the cardinality form used here.

Source application: the abelian-core branch of the faithful binary amalgams
in Aschbacher–Smith F.1.12 and F.6.5, printed pp.262–263 and 305.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conjugate_sup_of_index_three (T : Subgroup G)
    (hi : T.index = 3) (hn : ¬ T.Normal) :
    ∃ g : G, T ⊔ T.map (MulAut.conj g).toMonoidHom = ⊤ := by
  have hN : normalizer (T : Set G) ≠ ⊤ := fun h => hn (normalizer_eq_top_iff.mp h)
  have hex : ∃ g : G, g ∉ normalizer (T : Set G) := by
    by_contra! hh
    exact hN (eq_top_iff.mpr (fun g _ => hh g))
  obtain ⟨g,hg⟩ := hex
  have hne : T ≠ T.map (MulAut.conj g).toMonoidHom := by
    intro he
    exact hg (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  refine ⟨g,(isCoatom_of_index_three T hi).sup_eq_top_of_ne ?_ hne⟩
  apply isCoatom_of_index_three
  rw [index_map_of_bijective (MulAut.conj g).bijective,hi]

theorem center_card_bound_of_abelian_normal_subgroup
    (Q T Z : Subgroup G) [Q.Normal] [IsMulCommutative Q]
    (hi : T.index = 3) (hn : ¬ T.Normal)
    (hZQ : Z ≤ Q) (hZT : Z ≤ centralizer (T : Set G))
    (hz : 2 * Nat.card Z = Nat.card Q) :
    Nat.card Q ≤ 4 * Nat.card (center G) := by
  obtain ⟨g,hg⟩ := exists_conjugate_sup_of_index_three T hi hn
  let f := (MulAut.conj g).toMonoidHom
  let Z' := Z.map f
  have hZ'Q : Z' ≤ Q := by
    calc
      Z.map f ≤ Q.map f := map_mono hZQ
      _ = Q := (mem_normalizer_iff_map_conj_eq.mp
        (show g ∈ normalizer (Q : Set G) by rw [Q.normalizer_eq_top];trivial))
  have hcomm : Z' ≤ centralizer (Z : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hZQ hy⟩ : Q) ⟨x,hZ'Q hx⟩)
  have hF : Z ⊓ Z' ≤ center G := by
    intro x hx
    have hxc : T ⊔ T.map f ≤ centralizer ({x} : Set G) := by
      apply sup_le
      · intro t ht
        rw [mem_centralizer_iff]
        rintro y (rfl : y = x)
        exact ((mem_centralizer_iff.mp (hZT hx.1)) t ht).symm
      · obtain ⟨z,hzZ,he⟩ := hx.2
        rintro _ ⟨t,ht,rfl⟩
        rw [mem_centralizer_iff]
        rintro y (rfl : y = x)
        rw [←he]
        exact (map_mul f _ _).symm.trans
          ((congrArg f (((mem_centralizer_iff.mp (hZT hzZ)) t ht).symm)).trans
            (map_mul f _ _))
    have htop : centralizer ({x} : Set G) = ⊤ := top_unique (hg ▸ hxc)
    exact centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton x)
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z Z'
    (hcomm.trans (centralizer_le_normalizer _))
  have he : Nat.card Z' = Nat.card Z := card_map_of_injective (MulAut.conj g).injective
  rw [he] at hp
  have hle := card_le_of_le (sup_le hZQ hZ'Q)
  have hfle := card_le_of_le hF
  have hpos := Nat.card_pos (α := Q)
  have hh : Nat.card Z * Nat.card Z ≤ Nat.card (center G) * Nat.card Q := by
    rw [hp]
    exact Nat.mul_le_mul hfle hle
  nlinarith

end Subgroup
