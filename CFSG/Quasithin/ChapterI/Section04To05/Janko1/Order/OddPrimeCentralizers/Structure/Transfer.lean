module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.TwoPart
public import Mathlib.GroupTheory.Transfer

/-!
# The actual odd complement in an odd-prime centralizer

The preceding two-part calculation makes `⟨z⟩` a Sylow two-subgroup
of `C_G(x)`. Burnside transfer gives a normal odd kernel complementary
to it. The image of the odd-order element `x` in the two-element
transfer target is trivial, so the kernel contains `x`.

Intersecting the ambient kernel with `C_G(z)` gives exactly `⟨x⟩`:
this odd intersection has order dividing `2p`, and contains `⟨x⟩`.
All normality here is relative to `C_G(x)`. The cyclicity and possible
orders of the complement are not asserted by this module.

Source: Bender, *Finite groups with large subgroups* (1974), (4.1),
printed p.225; Janko (1966), proof of Lemma 3.1.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The normal odd complement to `⟨z⟩` in the actual ambient centralizer.
No cyclicity or bound on the odd order is included in this intermediate statement. -/
public structure OddCentralizerComplement (x : G) (A : Subgroup G) : Prop where
  odd_card : Odd (Nat.card A)
  x_mem : x ∈ A
  normalizes : centralizer ({x} : Set G) ≤ normalizer (A : Set G)
  disjoint : Disjoint A (zpowers h.z)
  sup_eq : A ⊔ zpowers h.z = centralizer ({x} : Set G)

/-- Burnside transfer constructs the odd complement before any classification
of that complement is used. -/
public theorem exists_oddCentralizerComplement (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    ∃ A : Subgroup G, OddCentralizerComplement h x A := by
  let C := centralizer ({x} : Set G)
  let zC : C := ⟨h.z, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp hxC).symm⟩
  obtain ⟨P, hP⟩ := h.exists_centralizer_sylow_eq_zpowers p hp x hxC hx
  have hP' : (P : Subgroup C) = zpowers zC := hP
  have hcyc : IsCyclic P := hP' ▸ inferInstance
  have hz : orderOf zC = 2 :=
    (orderOf_injective C.subtype Subtype.val_injective zC).symm.trans h.involution
  have hmin : (Nat.card C).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr (hz ▸ orderOf_dvd_natCard zC)
  let f := MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hmin)
  let K := f.ker
  let A := K.map C.subtype
  have hcomp : K.IsComplement' (P : Subgroup C) := hcyc.isComplement' hmin
  have hPmap : (P : Subgroup C).map C.subtype = zpowers h.z := by
    rw [hP', MonoidHom.map_zpowers]
    rfl
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Nat.card A = Nat.card K from card_map_of_injective Subtype.val_injective]
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact MonoidHom.not_dvd_card_ker_transferSylow P (hcyc.normalizer_le_centralizer hmin)
  · let xC : C := ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩
    have hxp : orderOf xC = p :=
      (orderOf_injective C.subtype Subtype.val_injective xC).symm.trans hx
    have hcardP : Nat.card P = 2 := by rw [hP', Nat.card_zpowers, hz]
    have hdivp : orderOf (f xC) ∣ p := hxp ▸ orderOf_map_dvd f xC
    have hdiv2 : orderOf (f xC) ∣ 2 := by simpa only [hcardP] using orderOf_dvd_natCard (f xC)
    have hcop : p.Coprime 2 := by rcases hp with rfl | rfl <;> decide
    have hfx : f xC = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop hdivp hdiv2)
    exact mem_map.mpr ⟨xC, hfx, rfl⟩
  · have hn := K.le_normalizer_map C.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, C.range_subtype] using hn
  · rw [← hPmap]
    exact disjoint_map Subtype.val_injective hcomp.disjoint
  · rw [← hPmap, ← Subgroup.map_sup, hcomp.sup_eq_top, ← MonoidHom.range_eq_map, C.range_subtype]

/-- The complement lies in the centralizer in which it was constructed. -/
public theorem OddCentralizerComplement.le_centralizer {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) : A ≤ centralizer ({x} : Set G) :=
  a.sup_eq ▸ le_sup_left

/-- The normality is relative to `C_G(x)`, not to the simple ambient group. -/
public theorem OddCentralizerComplement.normal_subgroupOf {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) :
    (A.subgroupOf (centralizer ({x} : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer a.le_centralizer).mpr a.normalizes

/-- The fixed subgroup of the distinguished involution in its odd complement
is exactly the given prime-order subgroup. -/
public theorem OddCentralizerComplement.inf_centralizer_eq_zpowers
    (p : ℕ) (hp : p = 3 ∨ p = 5) {x : G}
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    {A : Subgroup G} (a : OddCentralizerComplement h x A) :
    A ⊓ centralizer ({h.z} : Set G) = zpowers x := by
  let D := A ⊓ centralizer ({h.z} : Set G)
  have hdiv : Nat.card D ∣ 2 * p := by
    have hd := card_dvd_of_le (show D ≤
      centralizer ({h.z} : Set G) ⊓ centralizer ({x} : Set G) from
        le_inf inf_le_right (inf_le_left.trans a.le_centralizer))
    rwa [h.odd_prime_common_centralizer_card p hp x hxC hx] at hd
  have hodd : Odd (Nat.card D) :=
    Odd.of_dvd_nat a.odd_card (card_dvd_of_le (show D ≤ A from inf_le_left))
  have hdvp : Nat.card D ∣ p :=
    (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left hdiv
  have hpos : 0 < p := by rcases hp with rfl | rfl <;> decide
  have hxD : zpowers x ≤ D := zpowers_le.mpr ⟨a.x_mem, hxC⟩
  apply (eq_of_le_of_card_ge hxD ?_).symm
  rw [Nat.card_zpowers, hx]
  exact Nat.le_of_dvd hpos hdvp

end CFSG.Quasithin.Janko1CentralizerData
