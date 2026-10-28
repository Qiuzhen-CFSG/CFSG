module
public import Theory.SpecificGroups.PSL2.LargeOddInverter
/-!
# Odd prime-power inversion inside embedded products of PSL₂ groups

A nonidentity involution in a product has a nonidentity involution in at
least one coordinate. Put a large odd prime-power rotation in that factor
and the identity in the other. Its image under an injective product map
retains both its order and inversion by the original ambient involution.

Source: Aschbacher–Smith E.2.17, printed p.230, paired PSL₂ reduction.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
private theorem product_large_inverter
    {F : Type*} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p^n) (hl : 7 < Nat.card F)
    (hmod : Nat.card F % 8 = 1 ∨ Nat.card F % 8 = 7)
    (t : PSL(2,F) × PSL(2,F)) (ht : orderOf t = 2) :
    ∃ r a : ℕ, r.Prime ∧ r ≠ 2 ∧ 0 < a ∧ 3 < r^a ∧
      ∃ x : PSL(2,F) × PSL(2,F), orderOf x = r^a ∧ t*x*t⁻¹=x⁻¹ := by
  have ht2 : t^2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  by_cases ht1 : t.1 = 1
  · have htne : t.2 ≠ 1 := by
      intro he
      have hh : t = 1 := Prod.ext ht1 he
      rw [hh,orderOf_one] at ht
      omega
    have hb : orderOf t.2 = 2 := orderOf_eq_prime (congrArg Prod.snd ht2) htne
    obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ :=
      exists_large_odd_prime_power_inverted ho hF hl hmod t.2 hb
    refine ⟨r,a,hr,hr2,ha,hbig,(1,x),?_,?_⟩
    · simpa only [Prod.orderOf_mk,orderOf_one,Nat.lcm_one_left] using hx
    · apply Prod.ext
      · simp
      · exact hi
  · have ha : orderOf t.1 = 2 := orderOf_eq_prime (congrArg Prod.fst ht2) ht1
    obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ :=
      exists_large_odd_prime_power_inverted ho hF hl hmod t.1 ha
    refine ⟨r,a,hr,hr2,ha,hbig,(x,1),?_,?_⟩
    · simpa only [Prod.orderOf_mk,orderOf_one,Nat.lcm_one_right] using hx
    · apply Prod.ext
      · exact hi
      · simp

theorem exists_large_odd_prime_power_inverted_of_product_embedding
    {G F : Type*} [Group G] [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p^n) (hl : 7 < Nat.card F)
    (hmod : Nat.card F % 8 = 1 ∨ Nat.card F % 8 = 7)
    (f : PSL(2,F) × PSL(2,F) →* G) (hf : Function.Injective f)
    (t : G) (ht : orderOf t = 2) (htf : t ∈ f.range) :
    ∃ r a : ℕ, r.Prime ∧ r ≠ 2 ∧ 0 < a ∧ 3 < r^a ∧
      ∃ x : G, orderOf x = r^a ∧ t*x*t⁻¹=x⁻¹ := by
  obtain ⟨s,rfl⟩ := htf
  have hs : orderOf s = 2 := (orderOf_injective f hf s).symm.trans ht
  obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ := product_large_inverter ho hF hl hmod s hs
  refine ⟨r,a,hr,hr2,ha,hbig,f x,(orderOf_injective f hf x).trans hx,?_⟩
  simpa only [map_mul,map_inv] using congrArg f hi
private theorem product_large_inverter_odd
    {F : Type*} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p^n) (hl : 7 < Nat.card F)
    (t : PSL(2,F) × PSL(2,F)) (ht : orderOf t = 2) :
    ∃ r a : ℕ, r.Prime ∧ r ≠ 2 ∧ 0 < a ∧ 3 < r^a ∧
      ∃ x : PSL(2,F) × PSL(2,F), orderOf x = r^a ∧ t*x*t⁻¹=x⁻¹ := by
  have ht2 : t^2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  by_cases ht1 : t.1 = 1
  · have htne : t.2 ≠ 1 := by
      intro he
      have hh : t = 1 := Prod.ext ht1 he
      rw [hh,orderOf_one] at ht
      omega
    have hb : orderOf t.2 = 2 := orderOf_eq_prime (congrArg Prod.snd ht2) htne
    obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ :=
      exists_large_odd_prime_power_inverted_of_odd ho hF hl t.2 hb
    refine ⟨r,a,hr,hr2,ha,hbig,(1,x),?_,?_⟩
    · simpa only [Prod.orderOf_mk,orderOf_one,Nat.lcm_one_left] using hx
    · apply Prod.ext
      · simp
      · exact hi
  · have ha : orderOf t.1 = 2 := orderOf_eq_prime (congrArg Prod.fst ht2) ht1
    obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ :=
      exists_large_odd_prime_power_inverted_of_odd ho hF hl t.1 ha
    refine ⟨r,a,hr,hr2,ha,hbig,(x,1),?_,?_⟩
    · simpa only [Prod.orderOf_mk,orderOf_one,Nat.lcm_one_right] using hx
    · apply Prod.ext
      · exact hi
      · simp

theorem exists_large_odd_prime_power_inverted_of_product_embedding_of_odd
    {G F : Type*} [Group G] [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p^n) (hl : 7 < Nat.card F)
    (f : PSL(2,F) × PSL(2,F) →* G) (hf : Function.Injective f)
    (t : G) (ht : orderOf t = 2) (htf : t ∈ f.range) :
    ∃ r a : ℕ, r.Prime ∧ r ≠ 2 ∧ 0 < a ∧ 3 < r^a ∧
      ∃ x : G, orderOf x = r^a ∧ t*x*t⁻¹=x⁻¹ := by
  obtain ⟨s,rfl⟩ := htf
  have hs : orderOf s = 2 := (orderOf_injective f hf s).symm.trans ht
  obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ := product_large_inverter_odd ho hF hl s hs
  refine ⟨r,a,hr,hr2,ha,hbig,f x,(orderOf_injective f hf x).trans hx,?_⟩
  simpa only [map_mul,map_inv] using congrArg f hi


end Theory.PSL2
