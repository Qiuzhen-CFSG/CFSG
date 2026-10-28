module

public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Conjugacy in cyclic prime extensions

Let C be a finite cyclic p-subgroup normalized, but not centralized, by an
element y of order p. For x in C with x^p = 1, every element of ⟨x,y⟩ outside
⟨x⟩ has a C-conjugate in ⟨y⟩.

For each nonidentity v in ⟨y⟩, the displacement c ↦ cvc⁻¹v⁻¹ is a nontrivial
homomorphism C → C. Its image has order divisible by p, so cyclicity forces
it to contain every p-th root of one in C. A displacement therefore cancels
the x-factor in a product from ⟨x⟩⟨y⟩. The product decomposition follows
because normalizers of finite cyclic groups preserve their subgroups.

This proves the conjugacy step used in GLS4, Chapter 2, Proposition 12.13,
equation (12H), `refs/KGroup/GLS4/Chapter2.tex`, lines 2305–2320. The source
uses the stronger odd-prime cyclic-extension structure from [I₁; 4.9]; the
conjugacy conclusion here holds for every prime.
-/

namespace Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem prime_root_is_displacement
    (C : Subgroup G) [IsCyclic C] (hC : IsPGroup p C)
    {v : G} (hvN : v ∈ normalizer (C : Set G))
    (hnon : ¬ C ≤ centralizer ({v} : Set G))
    {a : G} (ha : a ∈ C) (hap : a ^ p = 1) :
    ∃ c ∈ C, MulAut.conj c v * v⁻¹ = a := by
  let : CommGroup C := IsCyclic.commGroup
  let α : MulAut C := C.normalizerMonoidHom ⟨v, hvN⟩
  let f : C →* C := MonoidHom.id C / α.toMonoidHom
  have hf (c : C) : (f c : G) = MulAut.conj (c : G) v * v⁻¹ := by
    simp only [f, div_eq_mul_inv]
    change (c : G) * (v * (c : G) * v⁻¹)⁻¹ = _
    simp only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]
  have hr : f.range ≠ ⊥ := by
    intro he
    apply hnon
    intro c hc
    have hfc : f ⟨c, hc⟩ = 1 := by
      have hh : f ⟨c, hc⟩ ∈ f.range := ⟨⟨c, hc⟩, rfl⟩
      rwa [he, mem_bot] at hh
    have hh : c = v * c * v⁻¹ := congrArg Subtype.val (div_eq_one.mp hfc)
    exact mem_centralizer_singleton_iff.mpr (eq_mul_inv_iff_mul_eq.mp hh)
  have hd : p ∣ Nat.card f.range :=
    ((hC.to_subgroup f.range).card_eq_or_dvd).resolve_left
      (fun he => hr (f.range.eq_bot_of_card_eq he))
  have haR : (⟨a, ha⟩ : C) ∈ f.range := by
    apply mem_of_pow_card_eq_one_in_cyclic
    obtain ⟨n, hn⟩ := hd
    have hh : (⟨a, ha⟩ : C) ^ p = 1 := Subtype.ext hap
    rw [hn, pow_mul, hh, one_pow]
  obtain ⟨c, hc⟩ := haR
  exact ⟨c, c.property, (hf c).symm.trans (congrArg Subtype.val hc)⟩

/-- A prime-order normalizing element moves every element of the generated
plane outside the cyclic prime line into its own cyclic subgroup by conjugation
inside the cyclic p-group. The chosen torus element may have order dividing p. -/
public theorem cyclic_prime_extension_orbits
    (C : Subgroup G) [IsCyclic C] (hC : IsPGroup p C)
    {x : G} (hx : x ∈ C) (hxp : x ^ p = 1)
    {y : G} (hyN : y ∈ normalizer (C : Set G)) (hyorder : orderOf y = p)
    (hnon : ¬ C ≤ centralizer ({y} : Set G))
    {u : G} (hu : u ∈ zpowers x ⊔ zpowers y) :
    u ∈ zpowers x ∨ ∃ c ∈ C, MulAut.conj c u ∈ zpowers y := by
  have hxyN : zpowers y ≤ normalizer (zpowers x : Set G) :=
    zpowers_le.mpr (normalizer_le_normalizer_of_le_cyclic (zpowers x) C
      (zpowers_le.mpr hx) hyN)
  have hu' : u ∈ (zpowers x : Set G) * (zpowers y : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hxyN]
    exact hu
  obtain ⟨a, ha, v, hv, rfl⟩ := hu'
  by_cases hv1 : v = 1
  · apply Or.inl
    change a * v ∈ zpowers x
    rw [hv1, mul_one]
    exact ha
  have hvo : orderOf v = p :=
    ((Fact.out : p.Prime).eq_one_or_self_of_dvd _
      (hyorder ▸ orderOf_dvd_of_mem_zpowers hv)).resolve_left
        (fun hh => hv1 (orderOf_eq_one_iff.mp hh))
  have hvline : zpowers v = zpowers y :=
    eq_of_le_of_card_ge (zpowers_le.mpr hv) (by rw [Nat.card_zpowers, Nat.card_zpowers, hvo, hyorder])
  have hvnon : ¬ C ≤ centralizer ({v} : Set G) := by
    intro hc
    apply hnon
    intro c hcC
    have hcv : Commute c v := mem_centralizer_singleton_iff.mp (hc hcC)
    have hyv : y ∈ zpowers v := hvline.symm ▸ mem_zpowers y
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hyv
    exact mem_centralizer_singleton_iff.mpr (hcv.zpow_right n).eq
  have haC : a ∈ C := (zpowers_le.mpr hx) ha
  have hap : a ^ p = 1 := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  obtain ⟨c, hc, he⟩ := prime_root_is_displacement C hC
    ((zpowers_le.mpr hyN) hv) hvnon (C.inv_mem haC) (by rw [inv_pow, hap, inv_one])
  have hca : Commute c a := ((C.le_centralizer hc) a haC).symm
  have hconj : MulAut.conj c (a * v) = v := by
    rw [map_mul]
    have hfix : MulAut.conj c a = a := by
      rw [MulAut.conj_apply, hca.eq, mul_inv_cancel_right]
    rw [hfix, mul_inv_eq_iff_eq_mul.mp he, ← mul_assoc, mul_inv_cancel, one_mul]
  exact Or.inr ⟨c, hc, by rw [hconj]; exact hv⟩

end Subgroup
