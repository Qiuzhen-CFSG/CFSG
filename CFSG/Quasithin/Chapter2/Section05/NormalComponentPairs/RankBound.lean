module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallModelFacts
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct

/-!
# Elementary cardinal bound from the original small Sylow shapes

A dihedral or semidihedral Sylow group has a cyclic subgroup of index two.
Its elementary subgroups therefore have at most four elements. The bound
uses the literal component Sylow from source 2.5.8(3), and is applied to the
central involution orbit in 2.5.12.
Source: Aschbacher--Smith, printed pp.556--558.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup

/-- Both original Sylow shapes have elementary rank at most two. -/
theorem SourceSylowTwoShape.elementary_card_le_four
    {P : Type*} [Group P] (h : SourceSylowTwoShape P)
    (E : Subgroup P) (he : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
  let : IsElementaryAbelian 2 E := he
  have hp : ∀ x : E, x ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E)
  unfold SourceSylowTwoShape at h
  rcases h with ⟨m, hm, ⟨e⟩⟩ | h
  · have hb := DihedralGroup.card_le_four_of_square_eq_one (E.map e.toMonoidHom) (by
      rintro ⟨_, x, hx, rfl⟩
      apply Subtype.ext
      change e x ^ 2 = 1
      rw [← map_pow, show x ^ 2 = 1 from congrArg Subtype.val (hp ⟨x, hx⟩), map_one])
    rwa [Subgroup.card_map_of_injective e.injective] at hb
  · obtain ⟨e⟩ := h
    let R := Semidihedral.standardRotation 4 (by omega)
    have hi : (zpowers R).index = 2 := by
      have hh := (zpowers R).card_mul_index
      rw [Nat.card_zpowers, Semidihedral.standardRotation_order,
        Semidihedral.standardModel_card] at hh
      norm_num at hh ⊢
      omega
    have hb := Subgroup.card_le_four_of_pow_two_of_cyclic_index_two (zpowers R) hi
      (E.map e.toMonoidHom) (by
        rintro ⟨_, x, hx, rfl⟩
        apply Subtype.ext
        change e x ^ 2 = 1
        rw [← map_pow, show x ^ 2 = 1 from congrArg Subtype.val (hp ⟨x, hx⟩), map_one])
    rwa [Subgroup.card_map_of_injective e.injective] at hb

/-- The bound on an actual ambient subgroup contained in a source Sylow. -/
theorem SourceSylowTwoShape.ambient_elementary_card_le_four
    {G : Type*} [Group G] (P E : Subgroup G) (h : SourceSylowTwoShape P)
    (hEP : E ≤ P) (he : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
  let : IsElementaryAbelian 2 E := he
  have hh := h.elementary_card_le_four (E.subgroupOf P) (IsElementaryAbelian.subgroupOf hEP)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv] at hh

/-- The actual component restriction used by the source's Sylow-shape theorem. -/
theorem SourceSylowTwoShape.component_elementary_card_le_four
    {G : Type*} [Group G] (P K E : Subgroup G)
    (h : SourceSylowTwoShape (P.subgroupOf K))
    (hEP : E ≤ P) (hEK : E ≤ K) (he : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
  let : IsElementaryAbelian 2 E := he
  have hh := h.ambient_elementary_card_le_four (P.subgroupOf K) (E.subgroupOf K)
    (subgroupOf_mono K hEP) (IsElementaryAbelian.subgroupOf hEK)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv] at hh

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
