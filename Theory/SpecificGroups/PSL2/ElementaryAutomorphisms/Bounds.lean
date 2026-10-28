module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Bounds.Quotient
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Bounds.FieldInvolution
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Bounds.Sylow
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary two-subgroups of the actual binary PSL₂ automorphism group

Assume every automorphism of J = PSL₂(2ⁿ) is an inner automorphism followed
by a field automorphism. The imported quotient construction gives a split
surjection from Aut(J) to the cyclic field-automorphism group, with kernel
exactly Inn(J). An elementary two-subgroup disjoint from this kernel has
order at most two; every nonidentity member is inner-conjugate to the
half-degree Frobenius, which forces n even.

For the general bound, a two-subgroup of Inn(J) embeds in J and has order
at most 2ⁿ by the additive-field Sylow model. If an elementary subgroup D
contains an outer involution a, its inner intersection commutes with a.
The trivial center of J identifies this intersection with a two-subgroup
of the actual fixed group C_J(a), isomorphic to PSL₂(2^(n/2)). Thus the
kernel of D's field projection has order at most 2^(n/2), and its cyclic
image has order at most two. Since n ≥ 2, their product is at most 2ⁿ.
This uses the GF(2) Sylow case when n = 2, and does not assert that the
additive field involution is fixed-point-free.

These are conditional model bounds: inner-field coverage is the only
extra automorphism-classification premise. Source: GLS, Volume 2,
Theorem 26.24, Step 5 and the final contradiction,
`refs/KGroup/GLS2/ChapterG.tex`. The parent module owns unconditional
coverage assembly and transport to perfect central covers.
-/

namespace Theory.PSL2
open scoped IsMulCommutative

variable {K E : Type*} [Field K] [CharP K 2] [_root_.Group E]

private theorem conj_injective : Function.Injective (MulAut.conj : Group K →* _) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro g hg
  exact psl2_conj_eq_one_implies g hg

private noncomputable def innerLift (f : E →* MulAut (Group K))
    (hi : ∀ x, f x ∈ inner K) : E →* Group K :=
  (MonoidHom.ofInjective (conj_injective (K := K))).symm.toMonoidHom.comp
    (f.codRestrict (inner K) hi)

private theorem conj_innerLift (f : E →* MulAut (Group K))
    (hi : ∀ x, f x ∈ inner K) (x : E) :
    MulAut.conj (innerLift f hi x) = f x :=
  congrArg Subtype.val ((MonoidHom.ofInjective (conj_injective (K := K))).apply_symm_apply
    ⟨f x, hi x⟩)

private theorem innerLift_injective (f : E →* MulAut (Group K))
    (hi : ∀ x, f x ∈ inner K) (hf : Function.Injective f) :
    Function.Injective (innerLift f hi) := by
  intro x y h
  apply hf
  rw [← conj_innerLift f hi x, ← conj_innerLift f hi y, h]

private theorem innerLift_fixed (f : E →* MulAut (Group K))
    (hi : ∀ x, f x ∈ inner K) (a : MulAut (Group K))
    (hc : ∀ x, Commute (f x) a) (x : E) : a (innerLift f hi x) = innerLift f hi x := by
  apply conj_injective
  calc
    MulAut.conj (a (innerLift f hi x)) = a * MulAut.conj (innerLift f hi x) * a⁻¹ := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    _ = a * f x * a⁻¹ := by rw [conj_innerLift]
    _ = f x := by rw [← (hc x).eq, mul_assoc, mul_inv_cancel, mul_one]
    _ = MulAut.conj (innerLift f hi x) := (conj_innerLift f hi x).symm

/-- A two-subgroup consisting of inner automorphisms has order at most the field. -/
public theorem twoGroup_card_le_field_of_inner [Finite K]
    (D : Subgroup (MulAut (Group K))) (hD : IsPGroup 2 D)
    (hi : D ≤ inner K) : Nat.card D ≤ Nat.card K :=
  twoGroup_card_le_field_of_injective hD (innerLift D.subtype (fun x => hi x.property))
    (innerLift_injective D.subtype _ Subtype.coe_injective)

/-- Inner actors commuting with an outer involution embed in its actual fixed
group. In binary degree n this gives the square-root bound. -/
public theorem twoGroup_inner_centralizing_outer_card_le {n : ℕ} (hn : 2 ≤ n)
    (hcoverage : ∀ a : MulAut (BinaryGroup n),
      ∃ (g : BinaryGroup n) (σ : BinaryField n ≃+* BinaryField n),
        a = MulAut.conj g * fieldAut σ)
    {E : Type*} [_root_.Group E] (hE : IsPGroup 2 E)
    (f : E →* MulAut (BinaryGroup n)) (hf : Function.Injective f)
    (hi : ∀ x, f x ∈ inner (BinaryField n))
    (a : MulAut (BinaryGroup n)) (ha : a ^ 2 = 1)
    (houter : a ∉ inner (BinaryField n)) (hc : ∀ x, Commute (f x) a) :
    Nat.card E ≤ 2 ^ (n / 2) := by
  obtain ⟨g, σ, heq⟩ := hcoverage a
  obtain ⟨m, hm, hnm, ⟨e⟩⟩ := outer_fixed_model_of_semilinear hn a ha g σ heq
    (by simpa only [← mem_inner_iff] using houter)
  let ψ : E →* a.fixedSubgroup := (innerLift f hi).codRestrict _ fun x =>
    (MulAut.mem_fixedSubgroup a _).mpr (innerLift_fixed f hi a hc x)
  have hψ : Function.Injective ψ := fun x y h =>
    innerLift_injective f hi hf (congrArg Subtype.val h)
  have hb := twoGroup_card_le_field_of_injective hE (e.toMonoidHom.comp ψ)
    (e.injective.comp hψ)
  simpa only [GaloisField.card 2 m hm.ne', show n / 2 = m by omega] using hb

/-- The genuine automorphism group of PSL₂(2ⁿ) has no elementary two-subgroup
larger than 2ⁿ, assuming only inner-field coverage. This includes n = 2. -/
public theorem elementary_card_le_of_coverage {n : ℕ} (hn : 2 ≤ n)
    (hcoverage : ∀ a : MulAut (BinaryGroup n),
      ∃ (g : BinaryGroup n) (σ : BinaryField n ≃+* BinaryField n),
        a = MulAut.conj g * fieldAut σ)
    (D : Subgroup (MulAut (BinaryGroup n))) [IsElementaryAbelian 2 D] :
    Nat.card D ≤ 2 ^ n := by
  classical
  by_cases hi : D ≤ inner (BinaryField n)
  · simpa only [GaloisField.card 2 n (by omega : n ≠ 0)] using
      twoGroup_card_le_field_of_inner D (IsElementaryAbelian.isPGroup 2 D) hi
  · obtain ⟨a, haD, haouter⟩ := SetLike.not_le_iff_exists.mp hi
    let π := fieldProjectionOfCoverage hcoverage
    let f := π.comp D.subtype
    let j : f.ker →* MulAut (BinaryGroup n) := D.subtype.comp f.ker.subtype
    have hj : Function.Injective j := Subtype.coe_injective.comp Subtype.coe_injective
    have hjinner (x : f.ker) : j x ∈ inner (BinaryField n) := by
      rw [← fieldProjectionOfCoverage_ker hcoverage]
      exact x.property
    have hjcomm (x : f.ker) : Commute (j x) a := by
      exact congrArg Subtype.val (mul_comm (x : D) ⟨a, haD⟩)
    have hker : Nat.card f.ker ≤ 2 ^ (n / 2) :=
      twoGroup_inner_centralizing_outer_card_le hn hcoverage
        ((IsElementaryAbelian.isPGroup 2 D).to_subgroup f.ker) j hj hjinner a
        (elemPow_eq_one_of_isElementaryAbelian a haD) haouter hjcomm
    let : IsCyclic (BinaryField n ≃+* BinaryField n) := OuterSolvable.finiteFieldAut_isCyclic
    let : IsElementaryAbelian 2 f.range :=
      IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hrange : Nat.card f.range ≤ 2 := by
      apply Nat.le_of_dvd (by decide : 0 < 2)
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 f.range
    calc
      Nat.card D = Nat.card f.ker * Nat.card f.range := by
        rw [← Subgroup.index_ker, Subgroup.card_mul_index]
      _ ≤ 2 ^ (n / 2) * 2 := Nat.mul_le_mul hker hrange
      _ = 2 ^ (n / 2 + 1) := (pow_succ _ _).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)

/-- Each nonidentity member of an elementary subgroup disjoint from the inner
group is conjugate to the distinguished field involution. -/
public theorem elementary_disjoint_nonidentity_halfFrobenius {n : ℕ} (hn : 2 ≤ n)
    (hcoverage : ∀ a : MulAut (BinaryGroup n),
      ∃ (g : BinaryGroup n) (σ : BinaryField n ≃+* BinaryField n),
        a = MulAut.conj g * fieldAut σ)
    (D : Subgroup (MulAut (BinaryGroup n))) [IsElementaryAbelian 2 D]
    (hD : Disjoint D (inner (BinaryField n)))
    (a : MulAut (BinaryGroup n)) (ha : a ∈ D) (hne : a ≠ 1) :
    Even n ∧ orderOf (binaryHalfFrobenius n) = 2 ∧
      (∀ x : BinaryField n, binaryHalfFrobenius n x = x ^ (2 ^ (n / 2))) ∧
      ∃ c : BinaryGroup n,
        MulAut.congr (MulAut.conj c) (fieldAut (binaryHalfFrobenius n)) = a :=
  outer_involution_halfFrobenius_of_coverage hn hcoverage a
    (elemPow_eq_one_of_isElementaryAbelian a ha)
    (fun hi => hne (Subgroup.disjoint_def.mp hD ha hi))

end Theory.PSL2
