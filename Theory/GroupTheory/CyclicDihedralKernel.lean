module

public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Cyclic quotients with odd dihedral kernels

If N is normal in H, H/N is cyclic, and N has abelianization of order two,
then H' = N'. Indeed N/N' is a normal subgroup of order two in H/N', hence
central. The cyclic quotient H/N then makes H/N' abelian.

For a dihedral group of order 2r with r odd, the commutator is exactly its
rotation subgroup and has order r. Thus a finite group admitting a map to
a cyclic group with such a kernel has odd commutator subgroup. The map
need not be surjective. This is the algebra used in GLS IV, Chapter 2,
the proof of Lemma 15.3, for D/K and its actual outer-action map.
-/

public section
open Subgroup
open scoped commutatorElement

namespace DihedralGroup

/-- For odd rotation order the commutator subgroup is the whole rotation
subgroup, including the degenerate rotation order one. -/
theorem commutator_eq_rotations_of_odd {n : ℕ} (hn : Odd n) :
    _root_.commutator (DihedralGroup n) = zpowers (r 1) := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have hrot (i : ZMod n) : r i ∈ zpowers (r (1 : ZMod n)) := by
    have hi : r i = (r (1 : ZMod n)) ^ i.val := by simp
    rw [hi]
    exact pow_mem (mem_zpowers _) _
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    cases a <;> cases b <;>
      simp only [commutatorElement_def, inv_r, inv_sr, r_mul_r, r_mul_sr,
        sr_mul_r, sr_mul_sr] <;> exact hrot _
  · apply zpowers_le.mpr
    have hs : (r (1 : ZMod n)) ^ 2 ∈ _root_.commutator (DihedralGroup n) := by
      have hc := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top (r (1 : ZMod n))) (Subgroup.mem_top (sr (0 : ZMod n)))
      simpa [_root_.commutator_def, commutatorElement_def, pow_two] using hc
    obtain ⟨k, hk⟩ := hn
    have he : (r (1 : ZMod n) ^ 2) ^ (k + 1) = r 1 := by
      rw [← pow_mul, show 2 * (k + 1) = n + 1 by omega, pow_add, r_one_pow_n,
        one_mul, pow_one]
    exact he ▸ (_root_.commutator (DihedralGroup n)).pow_mem hs (k + 1)

/-- The commutator subgroup of D₂ₙ has order n when n is odd. -/
theorem card_commutator_of_odd {n : ℕ} (hn : Odd n) :
    Nat.card (_root_.commutator (DihedralGroup n)) = n := by
  rw [commutator_eq_rotations_of_odd hn, Nat.card_zpowers, orderOf_r_one]

/-- The abelianization of an odd dihedral group has order two. -/
theorem card_abelianization_of_odd {n : ℕ} (hn : Odd n) :
    Nat.card (Abelianization (DihedralGroup n)) = 2 := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  change (_root_.commutator (DihedralGroup n)).index = 2
  have he := (_root_.commutator (DihedralGroup n)).card_mul_index
  rw [card_commutator_of_odd hn, nat_card] at he
  exact (Nat.mul_left_cancel hn.pos (he.trans (Nat.mul_comm 2 n)))

end DihedralGroup

namespace Subgroup
variable {H : Type*} [Group H]

/-- A cyclic extension of a normal subgroup with abelianization of order
two introduces no new commutators. -/
theorem commutator_eq_of_cyclic_quotient_card_abelianization_two
    (N : Subgroup H) [N.Normal] [IsCyclic (H ⧸ N)]
    (hN : Nat.card (Abelianization N) = 2) :
    _root_.commutator H = (_root_.commutator N).map N.subtype := by
  let A : Subgroup H := ⁅N, N⁆
  let q := QuotientGroup.mk' A
  let c : N →* H ⧸ A := q.comp N.subtype
  have hker : c.ker = _root_.commutator N := by
    ext x
    change (x.val : H ⧸ A) = 1 ↔ x ∈ _root_.commutator N
    rw [QuotientGroup.eq_one_iff]
    change x.val ∈ ⁅N, N⁆ ↔ _
    rw [← map_subtype_commutator]
    constructor
    · rintro ⟨y, hy, he⟩
      exact (Subtype.ext he : y = x) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hrange : c.range = N.map q := by
    change (q.comp N.subtype).range = _
    rw [MonoidHom.range_comp, N.range_subtype]
  have hcard : Nat.card (N.map q) = 2 := by
    rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange c).toEquiv,
      hker]
    exact hN
  have hcentral : N.map q ≤ center (H ⧸ A) := central_of_normal_card_two _ hcard
  let f : H ⧸ A →* H ⧸ N := QuotientGroup.lift A (QuotientGroup.mk' N)
    (by simpa only [QuotientGroup.ker_mk'] using N.commutator_le_self)
  have hcentralKer : f.ker ≤ center (H ⧸ A) := by
    simpa only [f, QuotientGroup.ker_lift, QuotientGroup.ker_mk'] using hcentral
  have hcomm : IsMulCommutative (H ⧸ A) :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center hcentralKer
  apply le_antisymm
  · rw [map_subtype_commutator]
    exact Normal.quotient_commutative_iff_commutator_le.mp hcomm
  · rw [map_subtype_commutator, _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top

/-- An odd dihedral normal subgroup and cyclic quotient force an odd
commutator subgroup in the ambient group. -/
theorem odd_card_commutator_of_cyclic_quotient_dihedral
    [Finite H] (N : Subgroup H) [N.Normal] [IsCyclic (H ⧸ N)]
    {n : ℕ} (hn : Odd n) (e : N ≃* DihedralGroup n) :
    Odd (Nat.card (_root_.commutator H)) := by
  have hAb : Nat.card (Abelianization N) = 2 :=
    (Nat.card_congr e.abelianizationCongr.toEquiv).trans
      (DihedralGroup.card_abelianization_of_odd hn)
  rw [commutator_eq_of_cyclic_quotient_card_abelianization_two N hAb,
    card_map_of_injective N.subtype_injective]
  have he : (_root_.commutator N).map e.toMonoidHom = _root_.commutator (DihedralGroup n) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hc : Nat.card (_root_.commutator N) = n := by
    have hm := card_map_of_injective (f := e.toMonoidHom) e.injective
      (K := _root_.commutator N)
    rw [he, DihedralGroup.card_commutator_of_odd hn] at hm
    exact hm.symm
  rwa [hc]

end Subgroup

namespace MonoidHom

/-- The actual map version: no surjectivity is required, and the kernel
is identified with the odd dihedral model by a multiplicative equivalence. -/
theorem odd_card_commutator_of_cyclic_dihedral_kernel
    {H C : Type*} [Group H] [Finite H] [Group C] [IsCyclic C]
    (f : H →* C) {n : ℕ} (hn : Odd n) (e : f.ker ≃* DihedralGroup n) :
    Odd (Nat.card (_root_.commutator H)) := by
  let : IsCyclic (H ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).injective
  exact Subgroup.odd_card_commutator_of_cyclic_quotient_dihedral f.ker hn e

end MonoidHom
