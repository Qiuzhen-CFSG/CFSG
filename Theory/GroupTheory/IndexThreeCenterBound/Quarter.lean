module
public import Theory.GroupTheory.IndexThreeCenterBound
/-!
# A quarter-subgroup version of the index-three center estimate

Two conjugate Sylow subgroups generate the vertex. Intersecting the
corresponding centralizing subgroups and using the product formula gives
|Q| ≤ 16|Z(G)| when the original centralizing subgroup has index at most
four in Q. This is used for the one-abelian-core faithful binary amalgam.

Source application: Aschbacher–Smith F.1.12/F.6.5, printed pp.262–263,305.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem center_card_bound_of_quarter_subgroup
    (Q T Z : Subgroup G) [Q.Normal] [IsMulCommutative Q]
    (hi : T.index = 3) (hn : ¬ T.Normal)
    (hZQ : Z ≤ Q) (hZT : Z ≤ centralizer (T : Set G))
    (hz : Nat.card Q ≤ 4 * Nat.card Z) :
    Nat.card Q ≤ 16 * Nat.card (center G) := by
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
