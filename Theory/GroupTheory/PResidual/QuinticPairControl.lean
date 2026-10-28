module
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PrimeOrderConjugation
public import Theory.GroupTheory.PrimeRankCentralizer
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Mathlib.GroupTheory.IndexNormal
/-!
# Order-five control by a subnormal residual pair

Let A and B be subnormal two-perfect subgroups, each with cyclic-five
quotient by its two-core. Suppose their join has five-rank two, the ambient
five-rank is at most two, and N(B) has index two and normalizes A.
Every element of order five then belongs to their join.

Such an element lies in the index-two normalizer. On quotienting by the
ambient two-core, its five-group action on each cyclic-five image is trivial.
The full rank-two join contains this centralizing element. The ambient
two-core normalizes both subnormal two-perfect factors, allowing the
membership to lift through the same quotient using the two-residual.

Source application: Aschbacher--Smith 14.6.15, printed p.1034, the
prime-order closure of the central point's ordinary centralizer.
The source consumer is Quintic.ModuleGeometry.ResidualPointClosure.
-/
public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- An index-two stabilizer of a full-rank residual pair captures every
ambient element of order five. -/
theorem mem_sup_of_order_five_of_index_two_normalizer (A B : Subgroup D)
    (hA : A.IsSubnormal) (hB : B.IsSubnormal)
    (hcA : Nat.card (A ⧸ pCore 2 A) = 5)
    (hcB : Nat.card (B ⧸ pCore 2 B) = 5)
    (hi : (normalizer (B : Set D)).index = 2)
    (hn : normalizer (B : Set D) ≤ normalizer (A : Set D))
    (hr : primeRank 5 D ≤ 2) (hrK : primeRank 5 (A ⊔ B : Subgroup D) = 2)
    (hpA : IsPPerfect 2 A) (hpB : IsPPerfect 2 B)
    (hpK : IsPPerfect 2 (A ⊔ B : Subgroup D)) {x : D} (hx : orderOf x = 5) :
    x ∈ A ⊔ B := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let q := QuotientGroup.mk' (pCore 2 D)
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hnx : x ∈ normalizer (B : Set D) := by
    have hh := (normalizer (B : Set D)).pow_mem (sq_mem_of_index_two hi x) 3
    have he : (x^2)^3 = x := by
      rw [←pow_mul]
      change x^(5+1) = x
      rw [pow_succ,←hx,pow_orderOf_eq_one,one_mul]
    rwa [he] at hh
  have hcent (C : Subgroup D) (hc : Nat.card (C ⧸ pCore 2 C) = 5)
      (hs : C.IsSubnormal) (hnx : x ∈ normalizer (C : Set D)) :
      q x ∈ centralizer (C.map q : Set (D ⧸ pCore 2 D)) := by
    have hc' : Nat.card (C.map q) = 5 :=
      (Nat.card_congr (hs.quotientCoreImageEquiv 2).toEquiv).symm.trans hc
    let Y := (zpowers x).map q
    have hY : IsPGroup 5 Y := (IsPGroup.of_card (G := zpowers x) (n := 1)
      (by rw [Nat.card_zpowers,hx]; rfl)).map q
    have hnY : Y ≤ normalizer (C.map q : Set (D ⧸ pCore 2 D)) :=
      (map_mono (zpowers_le.mpr hnx)).trans (le_normalizer_map q)
    let : Normalizes Y (C.map q) := ⟨hnY⟩
    have hf := actsTrivially_of_isPGroup_on_cyclic_prime_order
      (A := Y) (G := C.map q) (by decide : Nat.Prime 5) hY
      (isCyclic_of_prime_card hc') hc'
    intro y hy
    have he := congrArg Subtype.val (hf
      ⟨q x,mem_map_of_mem q (mem_zpowers x)⟩ ⟨y,hy⟩)
    change q x*y*(q x)⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hximage : q x ∈ (A ⊔ B : Subgroup D).map q := by
    apply mem_of_prime_pow_eq_one_of_centralizes_rank_two
      ((primeRank_quotient_le_of_isTwoGroup 5 (by decide) (pCore 2 D) pCore_isPGroup).trans hr)
      _
    · rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 5) q hq]
      exact hrK
    · rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]
    · rw [Subgroup.map_sup]
      have hleft : A.map q ≤ centralizer {q x} := by
        intro y hy z hz
        have he : z = q x := hz
        rw [he]
        exact (hcent A hcA hA (hn hnx) y hy).symm
      have hright : B.map q ≤ centralizer {q x} := by
        intro y hy z hz
        have he : z = q x := hz
        rw [he]
        exact (hcent B hcB hB hnx y hy).symm
      intro y hy
      exact (sup_le hleft hright hy (q x) rfl).symm
  have hQK : q.ker ≤ normalizer ((A ⊔ B : Subgroup D) : Set D) := by
    rw [QuotientGroup.ker_mk']
    have hnA := le_normalizer_of_isSubnormal_isPPerfect A (pCore 2 D) hA hpA
      pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)
    have hnB := le_normalizer_of_isSubnormal_isPPerfect B (pCore 2 D) hB hpB
      pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)
    exact (le_inf hnA hnB).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hxp : x ∈ (A ⊔ B : Subgroup D) ⊔ q.ker := by
    have hm : x ∈ (((A ⊔ B : Subgroup D).map q).comap q) := hximage
    rwa [comap_map_eq] at hm
  rw [←embedded_pResidual_sup_kernel q (A ⊔ B) hpK hq hQK]
  refine ⟨⟨x,hxp⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
  rw [←Subgroup.orderOf_coe,hx]
  decide



end Subgroup
