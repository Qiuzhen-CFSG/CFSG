module

public import Theory.Character.TwoSectionMass
public import Theory.Character.InductionSpecialSupport
public import Theory.Character.Orthogonality

/-!
# Ordinary character norm budgets on two-sections

Distinct nonidentity two-sections of an irreducible character have total mass
strictly below one. No modular-block or section-completeness assumption is used.

Commuting two- and odd-order parts are unique: a common odd exponent kills both
odd parts, and powering by that exponent is invertible on the pair of two-parts.
Consequently transporters between elements of the local slice `u C(u)_{odd}`
centralize `u`. Special-support induction counts these conjugacy fibers and
identifies the centralizer average with the ambient section norm. Disjointness
and ordinary row orthogonality give the budget; the identity section supplies
the strict gap.

Source: the ordinary section-norm argument underlying P. Fong,
*Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), pp. 73–74. The counting implementation reuses this
repository's `Theory.Character.InductionSpecialSupport`.
-/

namespace Theory.Character
variable {G : Type*} [Group G]

private theorem twoParts_unique {u v t w : G} (hu : ∃ k : ℕ, u ^ (2^k) = 1)
    (ht : ∃ k : ℕ, t ^ (2^k) = 1) (hv : Odd (orderOf v))
    (hw : Odd (orderOf w)) (huv : Commute u v) (htw : Commute t w)
    (heq : u*v = t*w) : u = t := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨l, hl⟩ := ht
  have hp : (u,t) ^ (2^(k+l)) = 1 := by
    apply Prod.ext
    · change u ^ (2^(k+l)) = 1
      rw [pow_add, pow_mul, hk, one_pow]
    · change t ^ (2^(k+l)) = 1
      rw [Nat.add_comm k l, pow_add, pow_mul, hl, one_pow]
  have hcop : (orderOf v * orderOf w).Coprime (orderOf (u,t)) := by
    apply Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hp)
    exact ((Nat.coprime_two_right.mpr hv).mul_left
      (Nat.coprime_two_right.mpr hw)).pow_right _
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  have hm : u ^ (orderOf v * orderOf w) = t ^ (orderOf v * orderOf w) := by
    have h := congrArg (fun x => x ^ (orderOf v * orderOf w)) heq
    rw [huv.mul_pow, htw.mul_pow] at h
    have hv' : v ^ (orderOf v * orderOf w) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
    have hw' : w ^ (orderOf v * orderOf w) = 1 := by rw [Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    simpa only [hv', hw', mul_one] using h
  have hb₁ := congrArg Prod.fst hb
  have hb₂ := congrArg Prod.snd hb
  change (u ^ (orderOf v * orderOf w)) ^ b = u at hb₁
  change (t ^ (orderOf v * orderOf w)) ^ b = t at hb₂
  rw [← hb₁, ← hb₂, hm]

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable

/-- An element lies in the two-section based at `u` if it is conjugate to `uv`
for an odd-order element `v` commuting with `u`. -/
@[expose] public def InTwoSection (u g : G) : Prop :=
  ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u*v) g

private theorem twoParts_unique_conj {u v t w : G} (hu : ∃ k : ℕ, u ^ (2^k) = 1)
    (ht : ∃ k : ℕ, t ^ (2^k) = 1) (hv : Odd (orderOf v))
    (hw : Odd (orderOf w)) (huv : Commute u v) (htw : Commute t w)
    (c : G) (heq : (MulAut.conj c) (u*v) = t*w) :
    (MulAut.conj c) u = t := by
  apply twoParts_unique (v := (MulAut.conj c) v) (w := w) _ ht _ hw
    (huv.map (MulAut.conj c)) htw (by simpa only [map_mul] using heq)
  · obtain ⟨k, hk⟩ := hu
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · simpa only [MulEquiv.orderOf_eq] using hv

/-- Two sections based at two-elements can meet only when their bases are conjugate. -/
public theorem isConj_of_mem_twoSection {u t g : G} (hu : ∃ k : ℕ, u ^ (2^k) = 1)
    (ht : ∃ k : ℕ, t ^ (2^k) = 1) (hug : InTwoSection u g) (htg : InTwoSection t g) :
    IsConj u t := by
  obtain ⟨v, hv, huv, hvconj⟩ := hug
  obtain ⟨w, hw, htw, hwconj⟩ := htg
  obtain ⟨c, hc⟩ := isConj_iff.mp (hvconj.trans hwconj.symm)
  exact isConj_iff.mpr ⟨c, twoParts_unique_conj hu ht hv hw huv htw c hc⟩

private def twoSectionLocalSupport (u : G) : Set (Subgroup.centralizer ({u} : Set G)) :=
  {a | Odd (orderOf (u⁻¹ * (a : G)))}

private theorem twoSectionLocalSupport_commute (u : G) (a : Subgroup.centralizer ({u} : Set G)) :
    Commute u (u⁻¹ * (a : G)) :=
  (Commute.refl u).inv_right.mul_right
    (Subgroup.mem_centralizer_singleton_iff.mp a.property).symm

private theorem twoSectionLocalSupport_special (u : G) (hu : ∃ k : ℕ, u ^ (2^k) = 1) :
    ∀ a b : Subgroup.centralizer ({u} : Set G),
      a ∈ twoSectionLocalSupport u → b ∈ twoSectionLocalSupport u →
      ∀ c : G, c⁻¹ * (a : G) * c = (b : G) →
        c ∈ Subgroup.centralizer ({u} : Set G) := by
  intro a b ha hb c hc
  have h := twoParts_unique_conj hu hu ha hb (twoSectionLocalSupport_commute u a) (twoSectionLocalSupport_commute u b) c⁻¹
    (by simpa only [mul_inv_cancel_left, MulAut.conj_apply, inv_inv] using hc)
  simp only [MulAut.conj_apply, inv_inv] at h
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h' := congrArg (fun x => c*x) h
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h'.symm


private def twoSectionLocalCut (u : G) (χ : ClassFunction G) :
    ClassFunction (Subgroup.centralizer ({u} : Set G)) := by
  classical
  exact fun a => if a ∈ twoSectionLocalSupport u then χ a else 0

private theorem twoSectionLocalCut_isClassFunction (u : G) (χ : ClassFunction G) (hχ : IsClassFunction χ) :
    IsClassFunction (twoSectionLocalCut u χ) := by
  classical
  intro a c
  have hc : (MulAut.conj (c : G)) u = u :=
    mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_singleton_iff.mp c.property)
  have he : u⁻¹ * ((c : G) * (a : G) * (c : G)⁻¹) =
      (MulAut.conj (c : G)) (u⁻¹ * (a : G)) := by
    rw [map_mul, map_inv, hc]
    rfl
  have hmem : c*a*c⁻¹ ∈ twoSectionLocalSupport u ↔ a ∈ twoSectionLocalSupport u := by
    change Odd (orderOf (u⁻¹ * ((c : G) * (a : G) * (c : G)⁻¹))) ↔
      Odd (orderOf (u⁻¹ * (a : G)))
    rw [he, MulEquiv.orderOf_eq]
  simp only [twoSectionLocalCut, hmem]
  split_ifs
  · exact hχ (a : G) (c : G)
  · rfl


variable [Finite G]

private theorem induced_twoSectionLocalCut (u : G) (hu : ∃ k : ℕ, u ^ (2^k) = 1)
    (χ : ClassFunction G) (hχ : IsClassFunction χ) (g : G) :
    inducedClassFunction (Subgroup.centralizer ({u} : Set G)) (twoSectionLocalCut u χ) g =
      if InTwoSection u g then χ g else 0 := by
  classical
  let C := Subgroup.centralizer ({u} : Set G)
  by_cases hg : InTwoSection u g
  · rw [if_pos hg]
    obtain ⟨v, hv, huv, hvconj⟩ := hg
    let a : C := ⟨u*v, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Commute.refl u).mul_right huv |>.eq.symm)⟩
    have ha : a ∈ twoSectionLocalSupport u := by
      change Odd (orderOf (u⁻¹ * (u*v)))
      simpa only [inv_mul_cancel_left] using hv
    have hlocal := inducedClassFunction_eq_on_specialSupport C (twoSectionLocalSupport u)
      (twoSectionLocalSupport_special u hu) (twoSectionLocalCut u χ) (twoSectionLocalCut_isClassFunction u χ hχ)
      (by intro b hb; simp [twoSectionLocalCut, hb]) a ha
    obtain ⟨c, hc⟩ := isConj_iff.mp hvconj
    rw [← hc, inducedClassFunction_isClassFunction, hχ]
    exact hlocal.trans (if_pos ha)
  · rw [if_neg hg]
    unfold inducedClassFunction
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro c _
    split
    · next hc =>
      apply if_neg
      intro ha
      apply hg
      refine ⟨u⁻¹ * (c⁻¹*g*c), ha, twoSectionLocalSupport_commute u ⟨_, hc⟩, ?_⟩
      apply isConj_iff.mpr
      exact ⟨c, by simp [mul_assoc]⟩
    · rfl


/-- The centralizer average equals the ambient normalized squared norm on the actual
two-section. The transporter count is supplied by special-support induction and
Frobenius reciprocity. -/
public theorem twoSectionMass_eq_sum (u : G) (hu : ∃ k : ℕ, u ^ (2^k) = 1)
    (χ : ClassFunction G) (hχ : IsClassFunction χ) :
    twoSectionMass χ u =
      (Nat.card G : ℝ)⁻¹ * ∑ g : G, if InTwoSection u g then Complex.normSq (χ g) else 0 := by
  classical
  let C := Subgroup.centralizer ({u} : Set G)
  let uc : C := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have h := scalarProduct_inducedClassFunction C (twoSectionLocalCut u χ) hχ
  have hamb : scalarProduct G (inducedClassFunction C (twoSectionLocalCut u χ)) χ =
      ((Nat.card G : ℝ)⁻¹ * ∑ g : G,
        if InTwoSection u g then Complex.normSq (χ g) else 0 : ℝ) := by
    simp only [scalarProduct, C, induced_twoSectionLocalCut u hu χ hχ, ite_mul, zero_mul]
    simp only [← Complex.mul_conj, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_sum, Complex.ofReal_zero,
      apply_ite, Complex.star_def]
  have hloc : scalarProduct C (twoSectionLocalCut u χ) (fun a : C => χ (a : G)) =
      (twoSectionMass χ u : ℂ) := by
    unfold scalarProduct
    rw [← Equiv.sum_comp (Equiv.mulLeft uc) (fun a : C => twoSectionLocalCut u χ a * star (χ (a : G)))]
    have he (a : C) : (Equiv.mulLeft uc) a = uc*a := rfl
    simp only [he, twoSectionLocalCut, twoSectionLocalSupport, Set.mem_ofPred_eq,
      Subgroup.coe_mul, uc, inv_mul_cancel_left, Subgroup.orderOf_coe,
      ite_mul, zero_mul, Complex.star_def, Complex.mul_conj]
    simp only [twoSectionMass, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, C]
    rw [Subsingleton.elim (C.instFintypeSubtypeMemOfDecidablePred) (Fintype.ofFinite C)]
  exact Complex.ofReal_injective (hloc.symm.trans (h.symm.trans hamb))


/-- Distinct two-sections consume at most the squared norm of a class function.
The selected sections need not cover the group. -/
public theorem sum_twoSectionMass_le_norm {ι : Type*} [Fintype ι] (r : ι → G)
    (hr : ∀ i, ∃ k : ℕ, r i ^ (2^k) = 1)
    (hsep : ∀ i j, IsConj (r i) (r j) → i = j)
    (χ : ClassFunction G) (hχ : IsClassFunction χ) :
    ∑ i, twoSectionMass χ (r i) ≤
      (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (χ g) := by
  classical
  simp_rw [twoSectionMass_eq_sum _ (hr _) χ hχ]
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro g _
  by_cases hex : ∃ i, InTwoSection (r i) g
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : ¬ InTwoSection (r j) g := fun hj =>
        hji (hsep j i (isConj_of_mem_twoSection (hr j) (hr i) hj hi))
      simp [hj]
    · simp
  · have hn : ∀ i, ¬ InTwoSection (r i) g := by simpa using hex
    simpa [hn] using Complex.normSq_nonneg (χ g)

private theorem irreducible_normSq_average {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (χ g) = 1 := by
  have h := irreducibleCharacter_self hχ
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  simp only [characterProduct, Representation.representation_character_inv_eq_star_character,
    Complex.star_def, Complex.mul_conj] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_sum, Complex.ofReal_one] using h

omit [Finite G] in
private theorem irreducible_isClassFunction {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    IsClassFunction χ := by
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  exact ρ.char_conj

omit [Finite G] in
private theorem irreducible_apply_one_ne_zero {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    χ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let := hρ
  let := Subrepresentation.irreducible_module_nontrivial ρ
  rw [Representation.char_one]
  exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Fin n → ℂ)).ne'

/-- The identity-section mass together with any finite family of distinct
nonidentity two-sections is at most the ordinary irreducible row norm, namely one. -/
public theorem twoSectionMass_one_add_sum_le_one {ι : Type*} [Fintype ι] (r : ι → G)
    (hr : ∀ i, ∃ k : ℕ, r i ^ (2^k) = 1)
    (hne : ∀ i, r i ≠ 1)
    (hsep : ∀ i j, IsConj (r i) (r j) → i = j)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    twoSectionMass χ 1 + ∑ i, twoSectionMass χ (r i) ≤ 1 := by
  let s : Option ι → G := fun i => i.elim 1 r
  have hs : ∀ i, ∃ k : ℕ, s i ^ (2^k) = 1 := by
    intro i
    cases i with
    | none => exact ⟨0, by simp [s]⟩
    | some i => exact hr i
  have hss : ∀ i j, IsConj (s i) (s j) → i = j := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (hne j (by simpa [s] using hij.symm))
    | some i =>
      cases j with
      | none => exact False.elim (hne i (by simpa [s] using hij))
      | some j => exact congrArg some (hsep i j hij)
  have h := sum_twoSectionMass_le_norm s hs hss χ (irreducible_isClassFunction hχ)
  rw [irreducible_normSq_average hχ] at h
  simpa [s, Fintype.sum_option] using h

/-- The masses of distinct nonidentity two-sections of an actual irreducible
character sum to strictly less than one. The omitted identity section has
positive mass because the irreducible degree is nonzero. -/
public theorem sum_twoSectionMass_lt_one {ι : Type*} [Fintype ι] (r : ι → G)
    (hr : ∀ i, ∃ k : ℕ, r i ^ (2^k) = 1)
    (hne : ∀ i, r i ≠ 1)
    (hsep : ∀ i j, IsConj (r i) (r j) → i = j)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    ∑ i, twoSectionMass χ (r i) < 1 := by
  have h := twoSectionMass_one_add_sum_le_one r hr hne hsep hχ
  have hp := twoSectionMass_one_pos χ (irreducible_apply_one_ne_zero hχ)
  linarith

end
end Theory.Character
