module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Seed
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.PGroup.OmegaImage

/-!
# Odd-prime torsion in the paired-component exclusion

The subgroup used in 11.3.5(2) is the ambient image of Ω₁(Oₚ(A)), for
an odd prime dividing q - 1. The genuine preceding 11.0.4 residual clauses
put it in L, including the separate cubic clause in the SL₃ branch.
This does not use the later rank-one natural marking of the omega orbit.

For abelian A the subgroup consists exactly of its p-torsion. Its image
in the literal L/O₂(L) is faithful. Consequently a single common power
action in that quotient lifts to the same ambient conjugator, and forces
all nonidentity p-torsion points to be fixed or none of them to be fixed.
The common power remains an explicit input until the actual SL₃/Sp₄
Cartan action is constructed; it is not a property of arbitrary p-plane
automorphisms.

Source: Aschbacher--Smith, 11.0.4 and 11.3.5(2), printed pp.760,771--772.
The earlier residual clauses are produced by the natural local-geometry
campaign. Their discharge and the remaining paired Hall and marking
constructions stay with the parameter-component and linear-geometry owners.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G]

/-- The literal ambient image of Ω₁(Oₚ(A)), with p retained explicitly. -/
def primeTorsion (A : Subgroup G) (p : ℕ) : Subgroup G :=
  (omega₁ (A.pCoreIn p) (p := p)).map (A.pCoreIn p).subtype

/-- The ambient definition is exactly the image of the intrinsic
Ω₁(Oₚ(A)) through both original subgroup inclusions. -/
theorem primeTorsion_eq_intrinsic (A : Subgroup G) (p : ℕ) :
    primeTorsion A p =
      ((omega₁ (pCore p A) (p := p)).map (pCore p A).subtype).map A.subtype := by
  let e : pCore p A ≃* A.pCoreIn p :=
    equivMapOfInjective (pCore p A) A.subtype A.subtype_injective
  have he := e.map_omega p 1
  simp only [primeTorsion, omega₁]
  rw [← he, map_map, map_map]
  congr 1

theorem primeTorsion_le (A : Subgroup G) (p : ℕ) : primeTorsion A p ≤ A :=
  (map_subtype_le _).trans (pCoreIn_le p A)

theorem primeTorsion_normalizer (A : Subgroup G) (p : ℕ) :
    normalizer (A : Set G) ≤ normalizer (primeTorsion A p : Set G) := by
  let : (omega₁ (A.pCoreIn p) (p := p)).Characteristic := omega₁_characteristic _
  exact (normalizer_le_normalizer_characteristic_image A (pCore p A)).trans
    (normalizer_le_normalizer_characteristic_image (A.pCoreIn p) (omega₁ _ (p := p)))

theorem primeTorsion_isPGroup (A : Subgroup G) (p : ℕ) [Fact p.Prime] :
    IsPGroup p (primeTorsion A p) :=
  ((isPGroup_pCoreIn p A).to_subgroup _).map _

theorem primeTorsion_elementary (A : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative A] : IsElementaryAbelian p (primeTorsion A p) := by
  let : IsMulCommutative (A.pCoreIn p) :=
    inferInstanceAs (IsMulCommutative ((pCore p A).map A.subtype))
  let : IsElementaryAbelian p (omega₁ (A.pCoreIn p) (p := p)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  exact IsElementaryAbelian.map _

/-- In an abelian Hall subgroup, the literal omega-core consists exactly of
the elements killed by p. Higher p-power exponents are not discarded. -/
theorem mem_primeTorsion_iff [Finite G] (A : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative A] (x : G) : x ∈ primeTorsion A p ↔ x ∈ A ∧ x ^ p = 1 := by
  constructor
  · intro hx
    let := primeTorsion_elementary A p
    exact ⟨primeTorsion_le A p hx, elemPow_eq_one_of_isElementaryAbelian x hx⟩
  · rintro ⟨hx,hxp⟩
    let a : A := ⟨x,hx⟩
    have hap : a ^ p = 1 := Subtype.ext hxp
    have hz : IsPGroup p (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hap)
    have hle : zpowers a ≤ pCore p A := le_sSup ⟨inferInstance,hz⟩
    have hc : a ∈ pCore p A := hle (mem_zpowers a)
    have hxc : x ∈ A.pCoreIn p := mem_map_of_mem A.subtype hc
    refine ⟨⟨x,hxc⟩,subset_closure ?_,rfl⟩
    change (⟨x,hxc⟩ : A.pCoreIn p) ^ (p ^ 1) = 1
    apply Subtype.ext
    simpa only [coe_pow, coe_one, pow_one] using hxp

/-- Cauchy's theorem supplies nontrivial p-torsion in the actual abelian
factor whenever p divides its order. -/
theorem primeTorsion_ne_bot [Finite G] (A : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative A] (hd : p ∣ Nat.card A) : primeTorsion A p ≠ ⊥ := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p hd
  have hne : (a : G) ≠ 1 := by
    intro he
    have he' : a = 1 := Subtype.ext he
    exact (Fact.out : p.Prime).ne_one (ha.symm.trans (by simp [he']))
  have hm : (a : G) ∈ primeTorsion A p := by
    apply (mem_primeTorsion_iff A p a).mpr
    refine ⟨a.property,?_⟩
    have hh := congrArg Subtype.val (pow_orderOf_eq_one a)
    simpa only [coe_pow, coe_one, ha] using hh
  intro he
  exact hne (mem_bot.mp (he ▸ hm))

private theorem primeTorsion_le_of_order (A N : Subgroup G) (p : ℕ) [Fact p.Prime]
    (h : ∀ a ∈ A, orderOf a = p → a ∈ N) : primeTorsion A p ≤ N := by
  rw [primeTorsion, map_le_iff_le_comap]
  apply (closure_le _).2
  intro a ha
  have hp : (a : G) ^ p = 1 := by
    simpa only [pow_one, coe_pow, coe_one] using congrArg Subtype.val ha
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hp) with he | he
  · change (a : G) ∈ N
    rw [orderOf_eq_one_iff.mp he]
    exact N.one_mem
  · exact h a (pCoreIn_le p A a.property) he

private theorem pow_element_mem_of_primeToResidual
    (A M N : Subgroup G) (hAM : A ≤ M) (p : ℕ)
    (hr : primeToResidual p M ≤ N.subgroupOf M)
    (a : G) (ha : a ∈ A) (hp : a ^ p = 1) : a ∈ N := by
  have hp' : (⟨a,hAM ha⟩ : M) ^ (p ^ 1) = 1 := by
    apply Subtype.ext
    simpa only [coe_pow, coe_one, pow_one] using hp
  exact hr (mem_primeToResidual_of_pow hp')

/-- The genuine 11.0.4 clauses place the paired Hall p-torsion in L.
No recognition of the outside component or its natural module is used. -/
theorem source_primeTorsion_le [Finite G]
    {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    primeTorsion A p ≤ L := by
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < S.field.degree := by have := S.nonbinary; omega
  have hpow : 1 ≤ 2 ^ S.field.degree := Nat.one_le_pow _ _ (by decide)
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have h2 : 2 ∣ 2 ^ S.field.degree := dvd_pow_self 2 (by omega)
    have hx := Nat.mod_eq_zero_of_dvd hd
    have hy := Nat.mod_eq_zero_of_dvd h2
    omega
  apply primeTorsion_le_of_order A L p
  intro a ha hoa
  have hap : a ^ p = 1 := hoa ▸ pow_orderOf_eq_one a
  rcases halt with hsl | hsp
  · by_cases hp3 : p = 3
    · rcases hp3 with rfl
      have he : Even S.field.degree := by
        by_contra hn
        have hm : 2 ^ S.field.degree % 3 = 2 := by
          obtain ⟨k,hk⟩ := Nat.not_even_iff_odd.mp hn
          rw [hk]
          simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
        have hx := Nat.mod_eq_zero_of_dvd hd
        omega
      exact hcubic hsl he a (hA ha).2 hoa
    · have hlarge : 3 < p := by have := hp.two_le; omega
      exact pow_element_mem_of_primeToResidual A _ L (hA.trans inf_le_right) p
        (hres p hp (.inl ⟨hsl,hd,hlarge⟩)).le a ha hap
  · have hd2 : p ∣ (2 ^ S.field.degree) ^ 2 - 1 :=
      hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
    exact pow_element_mem_of_primeToResidual A _ L (hA.trans inf_le_right) p
      (hres p hp (.inr ⟨hsp,hd2⟩)).le a ha hap

/-- The original quotient L/O₂(L) is faithful on this odd-primary subgroup. -/
theorem primeTorsion_quotient_injective (A L : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hL : primeTorsion A p ≤ L) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hL)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  apply mem_bot.mpr
  apply Subtype.ext
  have hq : (a : G) ∈ L.pCoreIn 2 := by
    have hx : inclusion hL a ∈ pCore 2 L :=
      (QuotientGroup.eq_one_iff _).mp ha
    exact mem_map_of_mem L.subtype hx
  exact disjoint_def.mp
    (IsPGroup.disjoint_of_ne p 2 hp2 (primeTorsion A p) (L.pCoreIn 2)
      (primeTorsion_isPGroup A p) (isPGroup_pCoreIn 2 L)) a.property hq

private theorem pow_fixed_iff_of_prime_order (p k : ℕ) [Fact p.Prime]
    {x : G} (hx : orderOf x = p) : x ^ k = x ↔ k % p = 1 := by
  nth_rw 2 [← pow_one x]
  rw [pow_inj_mod, hx, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]

/-- One common power on the literal p-torsion has either all or no
nonidentity fixed points. The power exponent must be common to every element. -/
theorem primeTorsion_power_dichotomy (A : Subgroup G) (p k : ℕ) [Fact p.Prime]
    [IsMulCommutative A] (t : G)
    (ha : ∀ x ∈ primeTorsion A p, t * x * t⁻¹ = x ^ k) :
    primeTorsion A p ≤ centralizer ({t} : Set G) ∨
      primeTorsion A p ⊓ centralizer ({t} : Set G) = ⊥ := by
  let := primeTorsion_elementary A p
  by_cases hk : k % p = 1
  · left
    intro x hx
    have hxp : x ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
    have he : x ^ k = x := by
      simpa only [pow_one] using pow_eq_pow_of_modEq (show k ≡ 1 [MOD p] by
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] using hk) hxp
    have ht : t * x = x * t := (mul_inv_eq_iff_eq_mul).mp ((ha x hx).trans he)
    exact mem_centralizer_singleton_iff.mpr ht.symm
  · right
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    by_contra hne
    have hxord : orderOf x = p := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian x hx.1) hne
    have ht := mem_centralizer_singleton_iff.mp hx.2
    apply hk
    apply (pow_fixed_iff_of_prime_order p k hxord).mp
    rw [← ha x hx.1, ← ht, mul_inv_cancel_right]

/-- A common power proved in the actual natural quotient lifts to the same
ambient conjugator on the odd p-torsion. -/
theorem primeTorsion_power_of_quotient (A L : Subgroup G) (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hL : primeTorsion A p ≤ L) (t : G)
    (ht : t ∈ normalizer (A : Set G))
    (ha : ∀ (x : G) (hx : x ∈ primeTorsion A p),
      QuotientGroup.mk' (pCore 2 L)
        ⟨t * x * t⁻¹, hL ((primeTorsion_normalizer A p ht x).mp hx)⟩ =
          (QuotientGroup.mk' (pCore 2 L) ⟨x,hL hx⟩) ^ k) :
    ∀ x ∈ primeTorsion A p, t * x * t⁻¹ = x ^ k := by
  intro x hx
  let a : primeTorsion A p := ⟨x,hx⟩
  let b : primeTorsion A p := ⟨t*x*t⁻¹,(primeTorsion_normalizer A p ht x).mp hx⟩
  have he : b = a ^ k := primeTorsion_quotient_injective A L p hp2 hL (by
    rw [map_pow]
    exact ha x hx)
  exact congrArg Subtype.val he

/-- The same field-power exponent in L/O₂(L) forbids simultaneous movement
and a nonidentity fixed point in the original ambient p-torsion. -/
theorem no_mixed_action_of_quotient_power (A L : Subgroup G) (p k : ℕ) [Fact p.Prime]
    [IsMulCommutative A] (hp2 : p ≠ 2) (hL : primeTorsion A p ≤ L) (t : G)
    (ht : t ∈ normalizer (A : Set G))
    (ha : ∀ (x : G) (hx : x ∈ primeTorsion A p),
      QuotientGroup.mk' (pCore 2 L)
        ⟨t*x*t⁻¹,hL ((primeTorsion_normalizer A p ht x).mp hx)⟩ =
          (QuotientGroup.mk' (pCore 2 L) ⟨x,hL hx⟩) ^ k)
    (hm : ¬ primeTorsion A p ≤ centralizer ({t} : Set G))
    (hf : primeTorsion A p ⊓ centralizer ({t} : Set G) ≠ ⊥) : False := by
  rcases primeTorsion_power_dichotomy A p k t
    (primeTorsion_power_of_quotient A L p k hp2 hL t ht ha) with he | he
  · exact hm he
  · exact hf he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
