module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic

/-!
# Filling a normal coset by a conjugacy class

An orbit contained in a coset fills that coset when the centralizer has the
corresponding order. For a normal subgroup of index four, the quotient is
abelian, so all conjugates stay in the original coset. If a subgroup covering
that quotient captures the outside involutions and their representative has
centralizer of order four there, it controls fusion in the involution coset.

The proof uses orbit–stabilizer and an injective map from the orbit to the
subgroup, given by multiplication by the inverse of the representative.
Source motivation: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.392,
the conjugacy count in the normalizer of the odd complement.
-/

namespace Subgroup

/-- A conjugacy class contained in a coset fills it when its orbit–stabilizer
count equals the size of that coset. -/
public theorem isConj_of_mul_inv_mem_of_centralizer_card {P : Type*} [Group P] [Finite P]
    (R : Subgroup P) (v : P)
    (hcomm : ∀ g : P, g * v * g⁻¹ * v⁻¹ ∈ R)
    (hcard : Nat.card P = Nat.card R * Nat.card (centralizer ({v} : Set P)))
    (u : P) (hu : u * v⁻¹ ∈ R) : IsConj u v := by
  let orbit := MulAction.orbit (ConjAct P) v
  let f : orbit → R := fun y => ⟨y.val * v⁻¹, by
    obtain ⟨g, hg⟩ := y.property
    rw [← hg]
    exact hcomm (ConjAct.ofConjAct g)⟩
  have hinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val hyz)
  have hstab : Nat.card (centralizer ({v} : Set P)) =
      Nat.card (MulAction.stabilizer (ConjAct P) v) := by
    rw [centralizer_eq_comap_stabilizer]
    rfl
  have hcount : Nat.card orbit * Nat.card (centralizer ({v} : Set P)) = Nat.card P := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct P) v)
    rw [Nat.card_prod, ← hstab] at hh
    exact hh
  have hsize : Nat.card R ≤ Nat.card orbit := by
    have hpos := Nat.card_pos (α := centralizer ({v} : Set P))
    nlinarith
  obtain ⟨y, hy⟩ := (hinj.bijective_of_nat_card_le hsize).surjective ⟨u * v⁻¹, hu⟩
  have hyu : y.val = u := mul_right_cancel (congrArg Subtype.val hy)
  obtain ⟨g, hg⟩ := y.property
  apply IsConj.symm
  exact isConj_iff.mpr ⟨ConjAct.ofConjAct g, hg.trans hyu⟩

/-- A group modulo a normal subgroup of index four is abelian. -/
public theorem conjugate_mul_inv_mem_of_index_four {P : Type*} [Group P] [Finite P]
    (K : Subgroup P) [K.Normal] (hK : K.index = 4) (g v : P) :
    g * v * g⁻¹ * v⁻¹ ∈ K := by
  let : IsMulCommutative (P ⧸ K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hK
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' K) (g * v * g⁻¹ * v⁻¹) = 1
  simp only [map_mul, map_inv]
  rw [IsMulCommutative.is_comm.comm ((QuotientGroup.mk' K) g) ((QuotientGroup.mk' K) v)]
  simp

/-- Local conjugacy control and the exact orbit size give fusion in the
coset obtained by adjoining an outside involution. -/
public theorem isConj_of_index_four_of_local_control {P : Type*} [Group P] [Finite P]
    (K H : Subgroup P) [K.Normal] (hK : K.index = 4) (hKH : K ≤ H)
    (v : P) (hv : orderOf v = 2) (hout : v ∉ H)
    (L : Subgroup P) (hvL : v ∈ L)
    (hcard : Nat.card L = Nat.card (K.subgroupOf L) *
      Nat.card (centralizer ({(⟨v, hvL⟩ : L)} : Set L)))
    (hmove : ∀ u : P, orderOf u = 2 → u ∉ H →
      ∃ w : L, IsConj u (w : P))
    (u : P) (hu : u ∈ K ⊔ zpowers v) (huK : u ∉ K) (huo : orderOf u = 2) :
    IsConj u v := by
  classical
  have hcoset : u * v⁻¹ ∈ K := by
    obtain ⟨k, hk, a, ha, rfl⟩ := mem_sup_of_normal_left.mp hu
    rw [mem_zpowers_iff_mem_range_orderOf, hv] at ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    have hn2 := Finset.mem_range.mp hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · exact (huK (by simpa using hk)).elim
    · simpa using hk
  have huH : u ∉ H := by
    intro hh
    have := H.mul_mem (H.inv_mem (hKH hcoset)) hh
    apply hout
    simpa using this
  obtain ⟨w, huw⟩ := hmove u huo huH
  have hwcoset : (w : P) * v⁻¹ ∈ K := by
    obtain ⟨g, hg⟩ := isConj_iff.mp huw
    rw [← hg]
    have hh := K.mul_mem (conjugate_mul_inv_mem_of_index_four K hK g u) hcoset
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  have hwv : IsConj w (⟨v, hvL⟩ : L) := by
    apply isConj_of_mul_inv_mem_of_centralizer_card (K.subgroupOf L) ⟨v, hvL⟩ _ hcard w hwcoset
    intro g
    exact conjugate_mul_inv_mem_of_index_four K hK (g : P) v
  exact huw.trans (L.subtype.map_isConj hwv)

/-- A subgroup covering a quotient of order four has the coset size required
by orbit–stabilizer when the representative's centralizer has order four. -/
public theorem card_eq_mul_centralizer_card_of_index_four {P : Type*} [Group P] [Finite P]
    (K L : Subgroup P) [K.Normal] (hK : K.index = 4)
    (hKL : K ⊔ L = ⊤) (v : L)
    (hC : Nat.card (centralizer ({v} : Set L)) = 4) :
    Nat.card L = Nat.card (K.subgroupOf L) * Nat.card (centralizer ({v} : Set L)) := by
  have hi : (K.subgroupOf L).index = 4 := by
    change K.relIndex L = 4
    rw [← relIndex_sup_left, hKL, relIndex_top_right, hK]
  have hh := (K.subgroupOf L).index_mul_card
  rw [hi] at hh
  rw [hC, Nat.mul_comm]
  exact hh.symm

end Subgroup
