module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder.Comparisons

/-!
# Fusion preserving a prime fixed subgroup

Fuse an involution to the marked involution, then adjust the conjugator
inside its centralizer using Sylow conjugacy at three or five. This
simultaneously identifies the involution and its chosen prime subgroup.
For an abelian odd complement, the adjusted conjugate centralizes the
marked generator and hence lies back in the same odd complement. Equality
of orders makes the conjugator an element of its ambient normalizer.

This is the ambient fusion step needed for the noncyclic-order restriction
in Bender (1974), proof of (4.1), printed p.225, citing Janko (1966),
proof of Lemma 3.1. Fusion is proved in the literal normalizer of A;
it is not inferred merely from ambient involution fusion.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Involution fusion can preserve the accompanying prime-order subgroup. -/
public theorem prime_fixed_pair_conjugate (h : Janko1CentralizerData G)
    (p : ℕ) (hp : p = 3 ∨ p = 5) (x : G)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (t : G) (ht : orderOf t = 2) (Y : Subgroup G) (hY : Nat.card Y = p)
    (hYt : Y ≤ centralizer ({t} : Set G)) :
    ∃ g : G, g * t * g⁻¹ = h.z ∧
      Y.map (MulAut.conj g).toMonoidHom = zpowers x := by
  have hpprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨s, hs⟩ := h.involutions_conjugate t ht
  let f := MulAut.conj s
  let C := centralizer ({h.z} : Set G)
  let Y' := Y.map f.toMonoidHom
  have hY'C : Y' ≤ C := by
    rintro w ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change f v * h.z = h.z * f v
    rw [← show f t = h.z from hs, ← map_mul, ← map_mul]
    exact congrArg f (mem_centralizer_singleton_iff.mp (hYt hv))
  have hUC : zpowers x ≤ C := zpowers_le.mpr hxC
  have sylow_of_prime (D : Subgroup G) (hDC : D ≤ C) (hD : Nat.card D = p) :
      ∃ P : Sylow p C, (P : Subgroup C) = D.subgroupOf C := by
    have hc : Nat.card (D.subgroupOf C) = p :=
      (Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hD
    have hi := (D.subgroupOf C).card_mul_index
    rw [hc, show Nat.card C = 120 from h.centralizer_card] at hi
    have hidx : ¬ p ∣ (D.subgroupOf C).index := by
      rcases hp with rfl | rfl <;> omega
    have hpD : IsPGroup p (D.subgroupOf C) :=
      IsPGroup.of_card (n := 1) (by simpa using hc)
    exact ⟨hpD.toSylow hidx, rfl⟩
  obtain ⟨P, hP⟩ := sylow_of_prime Y' hY'C (by
    rw [card_map_of_injective f.injective, hY])
  obtain ⟨Q, hQ⟩ := sylow_of_prime (zpowers x) hUC (by rw [Nat.card_zpowers, hx])
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq C P Q
  refine ⟨(n : G) * s, ?_, ?_⟩
  · calc
      ((n : G) * s) * t * ((n : G) * s)⁻¹ =
          (n : G) * (s * t * s⁻¹) * (n : G)⁻¹ := by group
      _ = (n : G) * h.z * (n : G)⁻¹ := by rw [hs]
      _ = h.z := by
        rw [mem_centralizer_singleton_iff.mp n.property,
          mul_assoc, mul_inv_cancel, mul_one]
  · apply eq_of_le_of_card_ge
    · rintro w ⟨v, hv, rfl⟩
      have hv' : f v ∈ Y' := mem_map.mpr ⟨v, hv, rfl⟩
      let vC : C := ⟨f v, hY'C hv'⟩
      have hvP : vC ∈ (P : Subgroup C) := by rw [hP]; exact hv'
      have hnQ : n * vC * n⁻¹ ∈ (Q : Subgroup C) := by
        rw [← hn]
        exact ⟨vC, hvP, rfl⟩
      rw [hQ] at hnQ
      change (n : G) * (s * v * s⁻¹) * (n : G)⁻¹ ∈ zpowers x at hnQ
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulAut.conj_apply, mul_inv_rev, mul_assoc] using hnQ
    · rw [card_map_of_injective (MulAut.conj _).injective, hY, Nat.card_zpowers, hx]

/-- An involution with the same prime fixed order fuses to z inside N_G(A). -/
public theorem OddCentralizerComplement.exists_normalizer_conj_of_fixed_card
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (ha : IsMulCommutative A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (t : G) (ht : orderOf t = 2)
    (hfixed : Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = p) :
    ∃ g ∈ normalizer (A : Set G), g * t * g⁻¹ = h.z := by
  let := ha
  let Y := A ⊓ centralizer ({t} : Set G)
  obtain ⟨g, hgt, hgY⟩ := h.prime_fixed_pair_conjugate p hp x hxC hx t ht Y hfixed
    inf_le_right
  let f := MulAut.conj g
  have hle : A.map f.toMonoidHom ≤ A := by
    rintro _ ⟨u, hu, rfl⟩
    apply (a.mem_iff_odd_orderOf ?_).mpr
    · change Odd (orderOf (f u))
      rw [f.orderOf_eq]
      exact a.odd_orderOf hu
    · have hxY : x ∈ Y.map f.toMonoidHom := hgY.symm ▸ mem_zpowers x
      obtain ⟨v, hv, hvx⟩ := hxY
      rw [mem_centralizer_singleton_iff, ← hvx, ← map_mul, ← map_mul]
      exact congrArg f ((Subgroup.le_centralizer A hu) v hv.1).symm
  have heq : A.map f.toMonoidHom = A :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective f.injective])
  exact ⟨g, mem_normalizer_iff_map_conj_eq.mpr heq, hgt⟩

end CFSG.Quasithin.Janko1CentralizerData
