module
public import Theory.Representation.Tits.FrobeniusDisplacement.GroupData
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ExceptionalCyclotomic
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.Application
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Source

/-!
# Excluding all remaining Ree field actors in A.3.18

The literal Ree order separates product-torus primes from cyclic-Sylow
primes; the latter contradict the component's rank. For a field actor of
prime order p, its scalar action has the same order, as detected on the
actual split torus. Its fixed field has odd degree (2m+1)/p. The natural
exceptional root maps embed the corresponding smaller Ree carrier into
the fixed subgroup of that SAME actor. Fermat's congruence transfers the
nonsplit product divisors, and the checked unitary and Suzuki tori supply
an elementary p-square there. At degree one, the certified Tits five-local
Frobenius pair gives the elementary subgroup of order 25 instead.

The faithful inner image of this square and the disjoint outside actor
have rank three in the original automorphism overgroup. The final transport
retains the literal component, its two-core quotient and outside element.
Thus the noncubic normal split-prime domain is complete, and every possible
outside actor is cubic. Genuine outer central cubic-cover diagonal clauses
remain explicit in `alternatives_or_outer_cubic_cover`.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.6, p.615;
GLS3 §§2.5–2.6 and §4.10 for the field and torus constructions. The imported
Tits word certificates record their ATLAS attribution and conventions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open ReeF4 ReeF4.ConverseParabolics.FullLeviRepresentation
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeNonsplit

private def torusMap {m : ℕ} (d : LocalBlockInput m) :
    (CoefficientField m)ˣ × (CoefficientField m)ˣ →* d.fixedGroup :=
  d.modelEquiv.symm.toMonoidHom.comp (torusHom m)

private theorem torusMap_injective {m : ℕ} (d : LocalBlockInput m) :
    Function.Injective (torusMap d) :=
  d.modelEquiv.symm.injective.comp (torusHom_injective m)

private theorem torusMap_mem {m : ℕ} (d : LocalBlockInput m)
    (x : (CoefficientField m)ˣ × (CoefficientField m)ˣ) :
    torusMap d x ∈ Cartan.torus d := by
  have ht := torusElement_mem x.1 x.2
  change toSplitGroup m (torusHom m x) ∈ Parabolics.splitTorus m at ht
  rw [Parabolics.splitTorus_eq_diagonalTorus] at ht
  change (torusMap d x).val ∈ Parabolics.diagonalTorus m
  have he : (torusMap d x).val = toSplitGroup m (torusHom m x) := by
    have hh := (d.modelEquiv_coe (torusMap d x)).symm
    simpa only [torusMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, toSplitGroup_apply] using hh
  rwa [he]

private theorem scalar_period {m : ℕ} (d : LocalBlockInput m) (r : ℕ)
    (hr : d.fieldAutomorphism ^ r = 1) :
    iterateFrobeniusEquiv (CoefficientField m) 2 r = 1 := by
  apply RingEquiv.ext
  intro x
  by_cases hx : x = 0
  · subst x; simp
  let u : (CoefficientField m)ˣ := Units.mk0 x hx
  have he := Cartan.field_torus_pow d (torusMap_mem d (u, 1)) r
  rw [hr, MulAut.one_apply, ← map_pow] at he
  have hu := congrArg Prod.fst (torusMap_injective d he)
  have hx' := congrArg Units.val hu
  exact hx'.symm

/-- An actual prime-order field actor fixes the embedded smaller Ree carrier. -/
theorem exists_fixed_carrier_embedding {m k p : ℕ} [Fact p.Prime]
    (d : LocalBlockInput m) (hnm : 2*m+1 = p*(2*k+1))
    (b : MulAut d.fixedGroup) (hb : orderOf b = p)
    (hfield : b ∈ zpowers d.fieldAutomorphism) :
    ∃ j : Model k →* d.fixedGroup, Function.Injective j ∧ ∀ x, b (j x) = j x := by
  obtain ⟨r, hr⟩ :=
    (isOfFinOrder_of_finite d.fieldAutomorphism).mem_powers_iff_mem_zpowers.mpr hfield
  change d.fieldAutomorphism ^ r = b at hr
  let σ := iterateFrobeniusEquiv (CoefficientField m) 2 r
  have hσp : σ ^ p = 1 := by
    have hbp : d.fieldAutomorphism ^ (r*p) = 1 := by
      rw [pow_mul, hr, ← hb, pow_orderOf_eq_one]
    simpa only [σ, iterateFrobeniusEquiv_eq_pow, ← pow_mul] using scalar_period d (r*p) hbp
  have hσ : orderOf σ = p := orderOf_eq_prime hσp (by
    intro hσ1
    have hb1 : b = 1 := by
      rw [← hr]
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      ext i j
      rw [Cartan.field_pow_entry]
      exact DFunLike.congr_fun hσ1 ((x.val.val : MatrixCarrier m) i j)
    rw [hb1, orderOf_one] at hb
    exact (Fact.out : p.Prime).ne_one hb.symm)
  let A := zpowers σ
  let F := FixedPoints.subfield A (CoefficientField m)
  let : Finite A := Finite.of_injective
    (fun a : A => (a.val : CoefficientField m → CoefficientField m))
    (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype A := Fintype.ofFinite A
  have hd : Module.finrank F (CoefficientField m) = p := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers, hσ]
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Module (ZMod 2) F := Algebra.toModule
  have ht := Module.finrank_mul_finrank (ZMod 2) F (CoefficientField m)
  rw [hd, GaloisField.finrank 2 (by omega : 2*m+1 ≠ 0)] at ht
  have hF : Module.finrank (ZMod 2) F = 2*k+1 := by
    have := (Fact.out : p.Prime).pos
    nlinarith
  have hdiv : Module.finrank (ZMod 2) (CoefficientField k) ∣ Module.finrank (ZMod 2) F := by
    rw [GaloisField.finrank 2 (by omega : 2*k+1 ≠ 0), hF]
  obtain ⟨j₀⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdiv
  let j := F.subtype.comp j₀.toRingHom
  have hj (t) : σ (j t) = j t := (j₀ t).property ⟨σ, mem_zpowers σ⟩
  have hdeg : 2*k+1 ∣ 2*m+1 := ⟨p, hnm.trans (Nat.mul_comm _ _)⟩
  let f : Model k →* d.fixedGroup :=
    d.modelEquiv.symm.toMonoidHom.comp (Subfield.reeMap hdeg j)
  refine ⟨f, d.modelEquiv.symm.injective.comp (Subfield.reeMap_injective hdeg j), ?_⟩
  intro x
  have he : (f x : SplitGroup m) = toSplitGroup m (Subfield.reeMap hdeg j x) := by
    have hh := (d.modelEquiv_coe (f x)).symm
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, toSplitGroup_apply] using hh
  rw [← hr]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i t
  rw [Cartan.field_pow_entry, he, Subfield.toSplitGroup_reeMap]
  exact hj (((toSplitGroup k x).val : MatrixCarrier k) i t)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeNonsplit

public noncomputable section
open Subgroup Theory.GroupTheory
open ReeF4 ReeF4.CentralCovers.OddPrimary
open GoodPrimeArithmetic
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeNonsplit

private theorem rank_le_one_of_cyclic_torus {m n c p : ℕ} [Fact p.Prime]
    (T : CyclicTorusEmbedding m n) (hn : 0 < n)
    (horder : Nat.card (Model m) = n*c) (hc : ¬ p ∣ c) :
    primeRank p (Model m) ≤ 1 := by
  let : NeZero n := ⟨hn.ne'⟩
  have hi : ¬ p ∣ T.map.range.index := by
    rw [torus_image_index T.map T.injective (by simp) horder]
    exact hc
  let P : Sylow p (Multiplicative (ZMod n)) := Classical.choice inferInstance
  have hindex : ¬ p ∣ ((P : Subgroup (Multiplicative (ZMod n))).map T.map).index := by
    rw [index_map_of_injective _ T.injective]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hi
  let R : Sylow p (Model m) := (P.isPGroup'.map T.map).toSylow hindex
  have hR : IsCyclic R := isCyclic_of_surjective
    (T.map.subgroupMap (P : Subgroup (Multiplicative (ZMod n)))) (T.map.subgroupMap_surjective _)
  exact R.primeRank_le_one_of_isCyclic hR

private theorem rank_le_one_phi12 {m p a b : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ (2^(2*m+1))^4 - (2^(2*m+1))^2 + 1)
    (ha : 0 < a) (hb : 0 < b)
    (hprod : a*b = (2^(2*m+1))^4 - (2^(2*m+1))^2 + 1)
    (hsep : ¬ (p ∣ a ∧ p ∣ b))
    (Ta : CyclicTorusEmbedding m a) (Tb : CyclicTorusEmbedding m b) :
    primeRank p (Model m) ≤ 1 := by
  let q := 2^(2*m+1)
  let c := q^12*(q-1)^2*(q+1)^2*(q^2+1)^2*(q^2-q+1)
  have hq : 1 ≤ q := one_le_pow₀ (by decide)
  have hc : ¬ p ∣ c := not_dvd_phi12_cofactor hq hp hd
  have ho : Nat.card (Model m) = (a*b)*c := by
    rw [Order.card_model, order_factorization _ hq, hprod]
    dsimp [q, c]
    ring
  rcases (Fact.out : p.Prime).dvd_mul.mp (hprod ▸ hd) with h | h
  · apply rank_le_one_of_cyclic_torus Ta ha (c := b*c)
    · rw [ho]; ring
    · exact (Fact.out : p.Prime).not_dvd_mul (fun ht => hsep ⟨h, ht⟩) hc
  · apply rank_le_one_of_cyclic_torus Tb hb (c := a*c)
    · rw [ho]; ring
    · exact (Fact.out : p.Prime).not_dvd_mul (fun ht => hsep ⟨ht, h⟩) hc

/-- Rank greater than one excludes the cyclic sixth and twelfth cyclotomic tori. -/
theorem product_prime_of_rank {m p : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (hp : 3 < p) (hr : 1 < primeRank p (Model m)) :
    p ∣ 2^(2*m+1)-1 ∨ p ∣ 2^(2*m+1)+1 ∨ p ∣ (2^(2*m+1))^2+1 := by
  have hd : p ∣ Nat.card (Model m) := by
    by_contra hn
    have he := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    omega
  have hf := prime_dvd_order_factors (Fact.out : p.Prime) hp ((Order.card_model m) ▸ hd)
  rcases hf with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · obtain ⟨T⟩ := (GoodPrimes.Unitary.Descent.nonempty_tori m hm).2
    let q := 2^(2*m+1)
    have hq : 1 ≤ q := one_le_pow₀ (by decide)
    have hh := rank_le_one_of_cyclic_torus T (Nat.succ_pos _)
      (c := q^12*(q-1)^2*(q+1)^2*(q^2+1)^2*(q^4-q^2+1)) (by
        rw [Order.card_model, order_factorization _ hq]
        dsimp [q]
        ring) (not_dvd_phi6_cofactor hq hp h)
    omega
  · have hh := rank_le_one_phi12 hp h (Cyclotomic.minusOrder_pos m)
      (Cyclotomic.plusOrder_pos m) (cyclotomic_factorization m)
      (cyclotomic_not_both hp) (Cyclotomic.minus_embedding m hm).some
      (Cyclotomic.plus_embedding m hm).some
    omega

private theorem elementary_of_product {G : Type*} [Group G]
    {p n : ℕ} [Fact p.Prime] [NeZero n] (hd : p ∣ n)
    (f : Multiplicative (ZMod n) × Multiplicative (ZMod n) →* G)
    (hf : Function.Injective f) :
    ∃ E : Subgroup G, IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card (Multiplicative (ZMod n)) by simpa using hd)
  let C := zpowers a
  let : IsElementaryAbelian p C := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (C × C) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p C) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p C) x.2) }
  let j := f.comp (C.subtype.prodMap C.subtype)
  have hj : Function.Injective j := hf.comp (fun x y h =>
    Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h)))
  let := IsElementaryAbelian.of_surjective (p := p) j.rangeRestrict j.rangeRestrict_surjective
  refine ⟨j.range, inferInstance, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
    Nat.card_prod, Nat.card_zpowers, ha, pow_two]

private theorem binary_five_plane :
    ∃ E : Subgroup (Model 0), IsElementaryAbelian 5 E ∧ Nat.card E = 5^2 := by
  let := Representation.TitsFrobeniusDisplacement.fiveKernel_elementary
  let f := Tits.InvolutionRootGeometry.embedding
  refine ⟨Tits.fiveKernel.map f, IsElementaryAbelian.map f, ?_⟩
  rw [card_map_of_injective Tits.InvolutionRootGeometry.embedding_injective, Tits.fiveKernel_card]
  norm_num

/-- The actual smaller Ree group has an elementary square at every nonsplit product prime. -/
theorem exists_elementary_nonsplit (k : ℕ) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hd : p ∣ 2^(2*k+1)+1 ∨ p ∣ (2^(2*k+1))^2+1) :
    ∃ E : Subgroup (Model k), IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  by_cases hk : 1 ≤ k
  · rcases hd with h | h
    · obtain ⟨T⟩ := (GoodPrimes.Unitary.Descent.nonempty_tori k hk).1
      exact elementary_of_product h T.map T.injective
    · have hprod := suzuki_factorization k
      rcases (Fact.out : p.Prime).dvd_mul.mp (hprod ▸ h) with h | h
      · obtain ⟨T⟩ := exists_suzuki_minus_productTorusEmbedding k hk
        exact elementary_of_product h T.map T.injective
      · obtain ⟨T⟩ := exists_suzuki_plus_productTorusEmbedding k hk
        exact elementary_of_product h T.map T.injective
  · have hk0 : k = 0 := by omega
    subst k
    have hp5 : p = 5 := by
      rcases hd with h | h
      · norm_num at h
        have := Nat.le_of_dvd (by decide : 0 < 3) h
        omega
      · norm_num at h
        exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp h).resolve_left (Fact.out : p.Prime).ne_one
    subst p
    exact binary_five_plane

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeNonsplit

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeNonsplit
open Subgroup Theory.GroupTheory ReeF4

/-- Both nonsplit product factors supply a square fixed by the same prime-order actor. -/
theorem exists_fixed_elementary {m p : ℕ} [Fact p.Prime]
    (d : LocalBlockInput m) (hp : 3 < p)
    (hd : p ∣ 2^(2*m+1)+1 ∨ p ∣ (2^(2*m+1))^2+1)
    (b : MulAut d.fixedGroup) (hb : orderOf b = p)
    (hfield : b ∈ zpowers d.fieldAutomorphism) :
    ∃ E : Subgroup d.fixedGroup, IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ b.fixedSubgroup := by
  let σ : zpowers d.fieldAutomorphism := ⟨b, hfield⟩
  have hσ : orderOf σ = p :=
    (orderOf_injective (zpowers d.fieldAutomorphism).subtype Subtype.val_injective σ).symm.trans hb
  have hdn : p ∣ 2*m+1 := by
    have h := orderOf_dvd_natCard σ
    rw [hσ, Nat.card_zpowers] at h
    exact h.trans d.orderOf_fieldAutomorphism_dvd
  obtain ⟨t, ht⟩ := hdn
  have hot : Odd t := Odd.of_dvd_nat (show Odd (2*m+1) from ⟨m, rfl⟩)
    ⟨p, ht.trans (Nat.mul_comm _ _)⟩
  obtain ⟨k, hk⟩ := hot
  have hnm : 2*m+1 = p*(2*k+1) := by rw [ht, hk]
  obtain ⟨j, hj, hfix⟩ := exists_fixed_carrier_embedding d hnm b hb hfield
  have hq : (2^(2*m+1) : ZMod p) = 2^(2*k+1) := by
    rw [hnm, Nat.mul_comm p, pow_mul, ZMod.pow_card]
  have hd' : p ∣ 2^(2*k+1)+1 ∨ p ∣ (2^(2*k+1))^2+1 := by
    rcases hd with h | h
    · left
      rw [← ZMod.natCast_eq_zero_iff] at h ⊢
      push_cast at h ⊢
      rwa [hq] at h
    · right
      rw [← ZMod.natCast_eq_zero_iff] at h ⊢
      push_cast at h ⊢
      rwa [hq] at h
  obtain ⟨E, hE, hcard⟩ := exists_elementary_nonsplit k hp hd'
  let := hE
  refine ⟨E.map j, IsElementaryAbelian.map j, ?_, ?_⟩
  · rw [card_map_of_injective hj, hcard]
  · rintro _ ⟨x, _, rfl⟩
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hfix x)

/-- The original automorphism overgroup contains rank three at a nonsplit product prime. -/
theorem field_actor_rank_three {m p : ℕ} [Fact p.Prime]
    (d : LocalBlockInput m) [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hp : 3 < p) (hd : p ∣ 2^(2*m+1)+1 ∨ p ∣ (2^(2*m+1))^2+1)
    (A : Subgroup (MulAut d.fixedGroup)) (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A)
    (b : MulAut d.fixedGroup) (hb : orderOf b = p)
    (hfield : b ∈ zpowers d.fieldAutomorphism) (hbA : b ∈ A)
    (hout : b ∉ MulAut.innerSubgroup d.fixedGroup) : 3 ≤ primeRank p A := by
  obtain ⟨E, hE, hcard, hfix⟩ := exists_fixed_elementary d hp hd b hb hfield
  let := hE
  let f : d.fixedGroup →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect)
      (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨b, hbA⟩
  have hx : orderOf x = p :=
    (orderOf_injective A.subtype A.subtype_injective x).symm.trans hb
  have hxB : x ∉ B := by
    rintro ⟨g, _, he⟩
    exact hout ⟨g, congrArg Subtype.val he⟩
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g, hg, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * b y * g⁻¹ = b (g * y * g⁻¹)
    rw [map_mul, map_mul, map_inv, hgfix]
  have hcB : Nat.card B = p^2 := by rw [card_map_of_injective hf, hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- Every remaining noncubic prime actor is inner under the actual SQTK rank bound. -/
theorem prime_actor_inner {m p : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (d : LocalBlockInput m) [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hp : 3 < p) (hr : 1 < primeRank p d.fixedGroup)
    (A : Subgroup (MulAut d.fixedGroup)) (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A)
    (hA : primeRank p A ≤ 2) (a : MulAut d.fixedGroup) (haA : a ∈ A) (ha : a^p = 1) :
    a ∈ MulAut.innerSubgroup d.fixedGroup := by
  by_contra hout
  have haorder : orderOf a = p := orderOf_eq_prime ha
    (fun he => hout (he ▸ (MulAut.innerSubgroup _).one_mem))
  obtain ⟨_, _, σ, _, _, hσA, hσ, hσout⟩ :=
    LocalBlockInput.exists_prime_field_representative hm d A hinner a haA haorder hout
  have hr' : 1 < primeRank p (Model m) := by rwa [primeRank_congr p d.modelEquiv] at hr
  rcases product_prime_of_rank hm hp hr' with hd | hd
  · have hh := ReeSplit.field_actor_rank_three d hd A hinner σ.val hσ σ.property hσA
    omega
  · have hh := field_actor_rank_three d hp hd A hinner σ.val hσ σ.property hσA hσout
    omega

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeNonsplit

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
variable {H : Type*} [Group H] [Finite H]

/-- The ordinary Ree row admits no noncubic outside prime actor under SQTK. -/
theorem ordinary_not_ree_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup d.fixedGroup := e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let f := normalAction K e
  have hb := hH.stronglyQuasithin p hp ho
  have hout := outside_action_not_inner hz hr hb e a ha haK
  have hfa : (f a)^p = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hpgt : 3 < p := by
    have := hp.two_le
    have := Nat.odd_iff.mp ho
    omega
  have hr' : 1 < primeRank p d.fixedGroup := by rw [central_model_rank hz e]; exact hr
  exact hout (ReeNonsplit.prime_actor_inner hm d hpgt hr' f.range
    (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
    (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩ hfa)

/-- Exclude Ree on the original component's literal two-core quotient. -/
theorem not_ree_twoCore_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At
      ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) m)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  exact ordinary_not_ree_model (twoCore_sqtk hH) hp ho hp3 hr' hz' hm
    ⟨d, ⟨(centralQuotientEquiv (twoCoreComponentEquiv hK)).trans e⟩⟩
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2

/-- All exceptional field actors are excluded. Only the genuine outer
central cubic-cover diagonal clauses remain. -/
theorem alternatives_or_outer_cubic_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ (p = 3 ∧ OuterCubicCoverActor (twoCoreComponent K)
      (QuotientGroup.mk' (pCore 2 H) a)) := by
  rcases alternatives_or_ree_or_cover hH hK hp ho hr a ha haK hgen with halt | hrem
  · exact Or.inl halt
  rcases hrem with ⟨hp3, hz, m, hm, _, hmodel⟩ | hcover
  · exact (not_ree_twoCore_model hH hK hp ho hp3 hr hz hm hmodel a ha haK).elim
  · exact Or.inr hcover

/-- Normal split-prime A.3.18 is complete for every prime other than three. -/
theorem alternatives_of_noncubic
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K :=
  (alternatives_or_outer_cubic_cover hH hK hp ho hr a ha haK hgen).resolve_right
    (fun h => hp3 h.1)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Subgroup Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

/-- The original outside split actor must be cubic. This uses the full component catalogue. -/
theorem prime_eq_three
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) : p = 3 := by
  rcases alternatives_or_outer_cubic_cover hH hK hp ho hr a ha haK hgen with halt | hcover
  · rcases (alternatives_iff a ha haK).mp halt with hprojective | hcover
    · exact hprojective.1
    · exact hcover.1
  · exact hcover.1

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
