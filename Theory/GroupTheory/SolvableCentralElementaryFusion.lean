module

public import Theory.GroupTheory.SolvableCentralOmegaSupplement

/-!
# Normal Sylow subgroups from central elementary fusion

In a finite solvable group, let E be elementary abelian and central in a
Sylow two-subgroup S. Suppose conjugates of elements of E which return to S
remain in E, and every odd subgroup normalized by E is trivial. Then S is
normal.

The odd-subgroup hypothesis kills the odd core. The central elementary
supplement theorem puts all conjugates of E in S, so the fusion hypothesis
makes E normal. Its centralizer is normal and contains S; Cauchy's theorem
and the odd-subgroup obstruction make this centralizer a two-group.

This is a solvable variant of the final Sylow-normality step in Parrott,
*A characterization of the Tits' simple group* (1972), §4, p.683, using the
central elementary supplement of Janko–Thompson (1970), Lemma 3.1.
-/

open Subgroup

/-- Central elementary fusion and an odd-subgroup obstruction force a normal Sylow. -/
public theorem Sylow.normal_of_central_elementary_fusion {G : Type*} [Group G] [Finite G]
    (hsol : Group.IsSolvable G) (S : Sylow 2 G)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hES : E ≤ S) (hEc : E ≤ centralizer (S : Set G))
    (hfusion : ∀ g x : G, x ∈ E → g * x * g⁻¹ ∈ (S : Subgroup G) →
      g * x * g⁻¹ ∈ E)
    (hodd : ∀ O : Subgroup G, Odd (Nat.card O) → E ≤ normalizer (O : Set G) →
      O = ⊥) : (S : Subgroup G).Normal := by
  have hcore : pPrimeCore 2 G = ⊥ := hodd _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) le_normalizer_of_normal
  obtain ⟨H, _, hEH, hcover, _, hcl⟩ :=
    exists_supplement_of_central_elementary_subgroup hsol S E hES hEc
  have hH : H = ⊤ := by simpa only [hcore, sup_bot_eq] using hcover
  have hEn : E.Normal := by
    constructor
    intro x hx g
    apply hfusion g x hx
    let xH : H := ⟨x, hEH hx⟩
    let gH : H := ⟨g, hH ▸ mem_top g⟩
    exact hcl (mem_map_of_mem H.subtype
      ((inferInstance : (normalClosure (E.subgroupOf H : Set H)).Normal).conj_mem xH
        (subset_normalClosure hx) gH))
  let := hEn
  let C := centralizer (E : Set G)
  have hCn : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    simpa only [normalizer_eq_top] using normalizer_le_normalizer_centralizer E
  let := hCn
  have hCp : IsPGroup 2 C := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
    intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    have hq2 : q = 2 := by
      by_contra hn
      let : Fact q.Prime := ⟨hqp⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) q hqd
      let O := (zpowers x).map C.subtype
      have hOo : Odd (Nat.card O) := by
        rw [card_map_of_injective C.subtype_injective, Nat.card_zpowers, hx]
        exact hqp.odd_of_ne_two hn
      have hEO : E ≤ normalizer (O : Set G) :=
        (le_centralizer_iff.mpr (map_subtype_le (zpowers x))).trans
          (centralizer_le_normalizer _)
      have hOb := hodd O hOo hEO
      have hxc : (x : G) = 1 := by
        have hm : (x : G) ∈ O := mem_map_of_mem C.subtype (mem_zpowers x)
        simpa only [hOb, mem_bot] using hm
      have hx1 : x = 1 := Subtype.ext hxc
      rw [hx1, orderOf_one] at hx
      exact hqp.ne_one hx.symm
    subst q
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩
  have hCS : C ≤ S := hCp.le_sylow_of_normal S
  have hSC : (S : Subgroup G) ≤ C := le_centralizer_iff.mp hEc
  exact (hCS.antisymm hSC) ▸ hCn
