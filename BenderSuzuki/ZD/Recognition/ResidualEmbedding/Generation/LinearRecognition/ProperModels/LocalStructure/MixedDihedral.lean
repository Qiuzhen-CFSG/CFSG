module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.Elementary
public import Theory.GroupTheory.DihedralHalfOrderClasses
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.InvolutionOddProduct
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Mixed involutions in the product-disconnected configuration

Let `A = ⟨Z ∩ M⟩` have exponent two, and suppose the involutions that are
products of two members of `Z` are exactly `Z`. If `z ∈ Z ∩ M` and the
involution `u` is outside `Z`, then `⟨u,z⟩` has order `4k`, with `k` odd,
or order eight. The canonical half-order power of `uz` is the unique
involution of `⟨uz⟩`. In the order-eight case it generates a subgroup of
`A` together with `z`, and `u ∈ M` does not centralize `A`.

Nonconjugacy makes the rotation order even. When it is divisible by four,
the half-order power preserves the reflection class of `z`. The product
hypothesis then places that power in `Z`, and its centralizer puts `u` in
`M`. Thus `(uz)²` is a product of two elements of `Z ∩ M`, and exponent
two of `A` forces the rotation order to be four. The cardinality argument
retains the possible odd factor and does not assume a two-group.

Source: GLS, Volume 4, Chapter 2, Lemma 12.2(e),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2021–2032. The parent local-structure
assembly supplies the exponent-two and product-set premises from the actual
models and the earlier local argument.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII Subgroup
universe v
variable {G : Type v} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Distinct involutions generate a subgroup with twice the rotation order. -/
private theorem mixed_pair_card {u z : G} (hu : PFAppendixIII.IsInvolution u) (hz : PFAppendixIII.IsInvolution z)
    (hne : u ≠ z) : Nat.card (closure ({u, z} : Set G)) = 2 * orderOf (u * z) := by
  let H := closure ({u, z} : Set G)
  let R := zpowers (u * z)
  have huH : u ∈ H := subset_closure (by simp)
  have hzH : z ∈ H := subset_closure (by simp)
  have hRH : R ≤ H := zpowers_le.mpr (H.mul_mem huH hzH)
  have hzR : z ∉ R := by
    intro hzR
    have huR : u ∈ R := by
      have hh := R.mul_mem (mem_zpowers (u * z)) hzR
      simpa only [mul_assoc, ← pow_two, hz.sq_eq_one, mul_one] using hh
    apply hne
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨u, huR⟩ : R)) (y := ⟨z, hzR⟩)
      (by rw [← orderOf_coe]; exact orderOf_eq_prime hu.sq_eq_one hu.ne_one)
      (by rw [← orderOf_coe]; exact orderOf_eq_prime hz.sq_eq_one hz.ne_one))
  have hlt : Nat.card R < Nat.card H := by
    apply lt_of_le_of_ne (card_le_of_le hRH)
    intro he
    have heq : R = H := eq_of_le_of_card_ge hRH he.ge
    exact hzR (heq.symm ▸ hzH)
  have hup : Nat.card H ≤ 2 * orderOf (u * z) := by
    have hh := (closure_pair_finite_card_le_of_involutions (orderOf_pos (u * z))
      z u hz.sq_eq_one hu.sq_eq_one (pow_orderOf_eq_one (u * z))).2
    simpa only [H, Set.pair_comm z u] using hh
  obtain ⟨k, hk⟩ := card_dvd_of_le hRH
  have hRcard : Nat.card R = orderOf (u * z) := Nat.card_zpowers _
  rw [hRcard] at hk hlt
  have hk2 : 2 ≤ k := by
    by_contra hn
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  nlinarith

omit [Finite G] in
private theorem mixed_mem_of_isConj (h : IsProductDisconnected Z M) {a b : G}
    (ha : a ∈ Z) (hc : IsConj a b) : b ∈ Z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  exact hg ▸ h.invariant g a ha

/-- The full mixed-involution conclusion of GLS4, Lemma 12.2(e), conditional
on exponent two of the distinguished closure and the established equality
`P = Z`. The two membership assertions in the final clause retain the
relative conclusion `u ∈ M \ C_M(A)`. -/
public theorem mixed_involution_dihedral_structure (h : IsProductDisconnected Z M) {z u : G}
    (hz : z ∈ Z) (hzM : z ∈ M)
    (hA2 : ∀ a ∈ closure (Z ∩ (M : Set G)), a ^ 2 = 1)
    (hP : {v : G | PFAppendixIII.IsInvolution v ∧ ∃ x ∈ Z, ∃ y ∈ Z, v = x * y} = Z)
    (hu : PFAppendixIII.IsInvolution u) (huZ : u ∉ Z) :
    let H := closure ({u, z} : Set G)
    let R := zpowers (u * z)
    let w := (u * z) ^ (orderOf (u * z) / 2)
    ((∃ k : ℕ, Odd k ∧ Nat.card H = 4 * k) ∨ Nat.card H = 8) ∧
      w ∈ R ∧ PFAppendixIII.IsInvolution w ∧
      (∀ v ∈ R, PFAppendixIII.IsInvolution v → v = w) ∧
      (Nat.card H = 8 → closure ({w, z} : Set G) ≤ closure (Z ∩ (M : Set G)) ∧
        u ∈ M ∧ u ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G)) := by
  let H := closure ({u, z} : Set G)
  let R := zpowers (u * z)
  let w := (u * z) ^ (orderOf (u * z) / 2)
  let A := closure (Z ∩ (M : Set G))
  change ((_ ∨ Nat.card H = 8) ∧ w ∈ R ∧ PFAppendixIII.IsInvolution w ∧
    (∀ v ∈ R, PFAppendixIII.IsInvolution v → v = w) ∧ _)
  have hzI := h.involutions z hz
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hn : ¬ IsConj u z := fun hc => huZ (mixed_mem_of_isConj h hz hc.symm)
  have hw := (half_order_involution_of_not_isConj u z hu2 hz2 hn).2
  have hwI : PFAppendixIII.IsInvolution w := (orderOf_eq_prime_iff.mp hw.1).symm
  have hwR : w ∈ R := npow_mem_zpowers _ _
  have hwM : w ∈ M := mem_of_commute h hz hzM hw.2.2.symm
  have hcard : Nat.card H = 2 * orderOf (u * z) :=
    mixed_pair_card hu hzI (fun he => huZ (he.symm ▸ hz))
  have heven : Even (orderOf (u * z)) := by
    rcases Nat.even_or_odd (orderOf (u * z)) with he | ho
    · exact he
    · exact False.elim (hn (isConj_of_involutions_odd_product u z hu.sq_eq_one hzI.sq_eq_one ho))
  have hfour (hdiv : orderOf (u * z) % 4 = 0) :
      orderOf (u * z) = 4 ∧ closure ({w, z} : Set G) ≤ A ∧ u ∈ M := by
    have hzwZ : z * w ∈ Z := by
      apply mixed_mem_of_isConj h hz
      simpa only [TwoInvolutionClassOrder.halfOrder_def, w] using
        (DihedralHalfOrderClasses.preserve hu2 hz2 hdiv).2
    have hwZ : w ∈ Z := by
      rw [← hP]
      refine ⟨hwI, z, hz, z * w, hzwZ, ?_⟩
      rw [← mul_assoc, ← pow_two, hzI.sq_eq_one, one_mul]
    have huM : u ∈ M := mem_of_commute h hwZ hwM hw.2.1
    have hconjZ : MulAut.conj u z ∈ Z := h.invariant u z hz
    have hconjM : MulAut.conj u z ∈ M := M.mul_mem (M.mul_mem huM hzM) (M.inv_mem huM)
    have hsquare : (u * z) ^ 2 ∈ A := by
      have hh := A.mul_mem (subset_closure ⟨hconjZ, hconjM⟩)
        (subset_closure ⟨hz, hzM⟩)
      simpa only [MulAut.conj_apply, hu.inv_eq_self, pow_two, mul_assoc] using hh
    have hpow4 : (u * z) ^ 4 = 1 := by
      simpa only [← pow_mul] using hA2 _ hsquare
    have hord : orderOf (u * z) = 4 := by
      have hd : orderOf (u * z) ∣ 4 := orderOf_dvd_of_pow_eq_one hpow4
      have hpos := orderOf_pos (u * z)
      have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
      omega
    refine ⟨hord, ?_, huM⟩
    apply (closure_le _).mpr
    intro x hx
    rcases (show x = w ∨ x = z by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with rfl | rfl
    · exact subset_closure ⟨hwZ, hwM⟩
    · exact subset_closure ⟨hz, hzM⟩
  refine ⟨?_, hwR, hwI, ?_, ?_⟩
  · by_cases hdiv : orderOf (u * z) % 4 = 0
    · right
      rw [hcard, (hfour hdiv).1]
    · left
      refine ⟨orderOf (u * z) / 2, ?_, ?_⟩
      · apply Nat.odd_iff.mpr
        obtain ⟨k, hk⟩ := heven
        omega
      · rw [hcard]
        obtain ⟨k, hk⟩ := heven
        omega
  · intro v hvR hvI
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨v, hvR⟩ : R)) (y := ⟨w, hwR⟩)
      (by rw [← orderOf_coe]; exact orderOf_eq_prime hvI.sq_eq_one hvI.ne_one)
      (by rw [← orderOf_coe]; exact hw.1))
  · intro hc8
    have ho4 : orderOf (u * z) = 4 := by
      rw [hcard] at hc8
      omega
    obtain ⟨_, hwzA, huM⟩ := hfour (by omega)
    refine ⟨hwzA, huM, ?_⟩
    intro huC
    have hzu : Commute z u := (mem_centralizer_iff.mp huC) z (subset_closure ⟨hz, hzM⟩)
    have hp2 : (u * z) ^ 2 = 1 := by
      rw [hzu.symm.mul_pow, hu.sq_eq_one, hzI.sq_eq_one, one_mul]
    have hd := orderOf_dvd_of_pow_eq_one hp2
    rw [ho4] at hd
    norm_num at hd
end BenderSuzuki.ZD
