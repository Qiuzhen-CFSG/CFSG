module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.SwappedSylow
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.SplitTorus.Swap

/-!
# Swapped Sylow tori in the actual projective unitary-three group

For a prime r other than two and three dividing q+1, take a Sylow subgroup
U of the cyclic norm-one field units. In an orthonormal frame, the literal
projective image of diag(a,b,(ab)⁻¹), for (a,b) in U × U, is injective:
its scalar kernel is cubic, whereas U is an r-group. The full projective
frame torus has index q³(q−1)(q²−q+1), which r does not divide. Thus the
image of U × U is Sylow in PSU₃.

The two coordinate generators are exchanged by the signed transposition
constructed in `SplitTorus.Swap`, transported by an actual special-unitary
multiplicative equivalence. This constructs `SwappedSylow` for the original
Hermitian form. Its central-cover consumer then excludes r from the kernel
of every finite perfect central cover. The argument works for every q,
so in particular for the requested odd prime powers with exponent one or two.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), printed pp.407–408
(PDF pp.418–419); GLS3 Theorem 6.1.4 and Tables 6.1.2–3. The concrete torus
and scalar quotient use `UnitaryThree.OddTorusNormalizer.Structure.ProjectiveTorus`.
The index and generator arguments also occur in the even-field large-prime bound.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External PerfectCentralCovering
open UnitaryThree.OddTorusNormalizer
open HermitianForm.EvenInner

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.SplitTorus
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private theorem cubic_factor {q : ℕ} (hq : 1 < q) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have hs := Nat.sub_add_cancel (show q ≤ q ^ 2 by nlinarith)
  have hh := congrArg (fun a : ℕ => (q + 1) * a) hs
  nlinarith

/-- The exact index of the full torus, with its scalar quotient retained. -/
theorem frameTorus_index (P : OrthogonalFrame J) {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    (projectiveFrameTorus J P).index = q ^ 3 * (q - 1) * (q ^ 2 - q + 1) := by
  have ht := projectiveFrameTorus_card J P q hcard (card_fixed J hcard hconj)
  have hG := card_projective J hcard hconj
  have hd := Nat.gcd_dvd_right 3 (q + 1)
  have hs : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  have he : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      Nat.card (projectiveFrameTorus J P) *
        (q ^ 3 * (q - 1) * (q ^ 2 - q + 1)) := by
    rw [hG, ht, cubic_factor hq, hs]
    calc
      _ = ((q + 1) * (q ^ 3 * (q - 1) * (q ^ 2 - q + 1))) * (q + 1) /
          Nat.gcd 3 (q + 1) := by congr 1; ring
      _ = _ := by rw [Nat.mul_div_assoc _ hd]; ring
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos
    ((projectiveFrameTorus J P).card_mul_index.trans he)

/-- Primes above three dividing q+1 do not divide the frame-torus index. -/
theorem not_dvd_frameTorus_index (P : OrthogonalFrame J) {q p : ℕ} (hq : 1 < q)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ q + 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    ¬ p ∣ (projectiveFrameTorus J P).index := by
  let : Fact p.Prime := ⟨hp⟩
  have hqmod : (q : ZMod p) = -1 := by
    have hz := (CharP.cast_eq_zero_iff (ZMod p) p (q + 1)).mpr hd
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  intro hi
  rw [frameTorus_index J P hq hcard hconj] at hi
  have hh := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hi
  have hle : q ≤ q ^ 2 := by nlinarith
  push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hle] at hh
  rw [hqmod] at hh
  have h6 : (6 : ZMod p) = 0 := by linear_combination hh
  have hd6 := (CharP.cast_eq_zero_iff (ZMod p) p 6).mp h6
  have : p = 2 ∨ p = 3 := by
    rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from hd6) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  omega

private theorem pair_generates {A G : Type*} [Group A] [Group G]
    (f : A × A →* G) (U : Subgroup A) (z : U)
    (hz : ∀ u : U, u ∈ zpowers z) :
    closure ({f (z, 1), f (1, z)} : Set G) = (U.prod U).map f := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(z, 1), ⟨z.property, U.one_mem⟩, rfl⟩
    · exact ⟨(1, z), ⟨U.one_mem, z.property⟩, rfl⟩
  · rintro g ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hz ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hz ⟨b, hb⟩)
    have hi' : (z : A) ^ i = a := congrArg Subtype.val hi
    have hj' : (z : A) ^ j = b := congrArg Subtype.val hj
    have he : f (a, b) = f ((z : A), 1) ^ i * f (1, (z : A)) ^ j := by
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext <;> simp [hi', hj']
    rw [he]
    exact mul_mem (zpow_mem (subset_closure (by simp)) i)
      (zpow_mem (subset_closure (by simp)) j)

omit [Finite F] in
/-- The literal projective map has trivial scalar kernel on the r-primary pair. -/
theorem sylowPair_injective (P : OrthogonalFrame J) {r : ℕ}
    (hr : r.Prime) (hr3 : r ≠ 3) (U : Sylow r (normOne J)) :
    Function.Injective ((projectivePairHom J P).comp
      ((U : Subgroup (normOne J)).prod (U : Subgroup (normOne J))).subtype) := by
  have hc : r.Coprime 3 := hr.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp hd))
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨a,b⟩, ha, hb⟩ h
  obtain ⟨hab, hb3⟩ := (projectivePairHom_eq_one_iff J P (a,b)).mp h
  have hb1 : (⟨b, hb⟩ : U) = 1 := by
    apply (U.isPGroup'.powEquiv hc).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using
      (show (⟨b, hb⟩ : U) ^ 3 = 1 from Subtype.ext hb3)
  have hb' : b = 1 := congrArg Subtype.val hb1
  exact Subtype.ext (Prod.ext (hab.trans hb') hb')

omit [Finite F] in
/-- Both cyclic Sylow factors survive projectivization without loss of order. -/
theorem sylowPair_card (P : OrthogonalFrame J) {r : ℕ}
    (hr : r.Prime) (hr3 : r ≠ 3) (U : Sylow r (normOne J)) :
    Nat.card (((U : Subgroup (normOne J)).prod (U : Subgroup (normOne J))).map
      (projectivePairHom J P)) = Nat.card U * Nat.card U := by
  have he := (Nat.card_congr
    (MonoidHom.ofInjective (sylowPair_injective J P hr hr3 U)).toEquiv).symm
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at he
  rw [he, Nat.card_congr (Subgroup.prodEquiv (U : Subgroup (normOne J))
    (U : Subgroup (normOne J))).toEquiv, Nat.card_prod]

/-- Construct the actual Sylow subgroup, its two generators and their ambient swapper. -/
theorem nonempty_swappedSylow {q r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hd : r ∣ q + 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    Nonempty (SwappedSylow J r) := by
  classical
  let : Fact r.Prime := ⟨hr⟩
  have hq : 1 < q := by
    have hf : 1 < Nat.card F := Finite.one_lt_card
    rw [hcard] at hf
    nlinarith
  obtain ⟨C, hC⟩ := huppert_II_10_4_a_orthonormal_basis 3 J q
    hcard (card_fixed J hcard hconj)
  let P : OrthogonalFrame J := ⟨C, hC⟩
  let U : Sylow r (normOne J) := Classical.choice inferInstance
  let R := (U : Subgroup (normOne J)).prod (U : Subgroup (normOne J))
  let H := R.map (projectivePairHom J P)
  have hi : ¬ r ∣ H.index := by
    rw [show H.index = (R ⊔ (projectivePairHom J P).ker).index *
        (projectivePairHom J P).range.index from index_map _ _, projectivePairHom_range]
    apply hr.not_dvd_mul _
      (not_dvd_frameTorus_index J P hq hr (by have := hr.two_le; omega) hd hcard hconj)
    intro hh
    have hdR : r ∣ R.index := hh.trans (index_dvd_of_le le_sup_left)
    rw [index_prod] at hdR
    exact hr.not_dvd_mul U.not_dvd_index U.not_dvd_index hdR
  obtain ⟨k, hk⟩ := U.isPGroup'.exists_card_eq
  have hH : IsPGroup r H := by
    apply IsPGroup.of_card (n := k + k)
    rw [show Nat.card H = Nat.card U * Nat.card U from sylowPair_card J P hr hr3 U,
      hk, pow_add]
  let Q := hH.toSylow hi
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := U)
  exact ⟨{
    sylow := Q
    x := projectivePairHom J P (z, 1)
    y := projectivePairHom J P (1, z)
    swapper := J.specialToProjective (signedSwap J P)
    generates := pair_generates _ _ z hz
    commute := (Commute.all ((z : normOne J), 1) (1, (z : normOne J))).map _
    swap_x := projective_signedSwap_pair J P _ _
    swap_y := projective_signedSwap_pair J P _ _ }⟩

/-- The q+1 branch of the odd cross-characteristic perfect-cover kernel bound. -/
theorem not_dvd_kernel_of_dvd_add_one {q r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hd : r ∣ q + 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨d⟩ := nonempty_swappedSylow J hr hr2 hr3 hd hcard hconj
  exact not_dvd_kernel_of_swapped_sylow J hr hr2 d f

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.SplitTorus
