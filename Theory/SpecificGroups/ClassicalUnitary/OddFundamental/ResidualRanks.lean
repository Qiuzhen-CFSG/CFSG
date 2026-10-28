module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.ResidualSetup
public import Theory.SpecificGroups.SU3.OddDefiningRank
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence

/-!
# Elementary abelian witnesses in a unitary fundamental centralizer residual

Write the ambient dimension as `2 + n`. For `n ≥ 3`, the complementary SUₙ
contains the additive field group, of order `r^(2e)`. In the antidiagonal
ternary model its coordinates are
`(x + σ x, x - σ x - (x + σ x)^2/2)`. Their multiplication is addition in `x`,
including in characteristic three. Huppert's orthonormal basis transports
this subgroup to the identity form, and extension by an identity block puts
it in the complementary SUₙ.

The faithful complementary map lands in the actual projective centralizer.
Every element of this additive image has r-th power one, so belongs to that
centralizer's intrinsic prime-to-r residual. Thus no identification of the
whole residual is needed to obtain rank at least `2e`. Together with the
complementary SU₂ bound, residual r-rank at most one forces `n = 1`, or
`n = 2` and `e = 1`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.2.17, printed p.39 (PDF p.50), the unitary case
of the deduction following (*). Matrix coordinates are Huppert II.10.12;
basis transport is Huppert II.10.4.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

private theorem unipotentSU_injective (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun g : J.specialSubgroup => g.val.val 0 1) h
  · exact congrArg (fun g : J.specialSubgroup => g.val.val 0 2) h

/-- The additive field embeds into the covering SU₃, before projectivization. -/
theorem exists_additive_embedding_three [Finite F] (h2 : (2 : F) ≠ 0)
    (q : ℕ) (hc : Nat.card F = q ^ 2)
    (hk : Nat.card {x : F // σ x = x} = q) :
    ∃ f : Multiplicative F →* (form σ hσ 3).specialSubgroup,
      Function.Injective f := by
  let J := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm (form σ hσ 3)
  obtain ⟨C, hC⟩ := huppert_II_10_4_a_orthonormal_basis 3 J q hc hk
  let e : J.specialSubgroup ≃* (form σ hσ 3).specialSubgroup :=
    IdentityGram.specialEquiv J C hC
  let f := (hermitianUnipotentSU J rfl).comp (OddDefiningRank.additiveCoordinates J h2)
  exact ⟨e.toMonoidHom.comp f, e.injective.comp
    ((unipotentSU_injective J rfl).comp (OddDefiningRank.additiveCoordinates_injective J h2))⟩

private theorem additive_pow {r : ℕ} [CharP F r] (x : Multiplicative F) :
    x ^ r = 1 := by
  change r • x.toAdd = 0
  simp [nsmul_eq_mul]

/-- The concrete additive field image lies in the literal centralizer residual:
its elements are killed by r, so lie in every normal subgroup of r′ index. -/
theorem exists_additive_embedding_residual [Finite F] {r n : ℕ} [CharP F r]
    (hn : 3 ≤ n) (h2 : (2 : F) ≠ 0) (q : ℕ) (hc : Nat.card F = q ^ 2)
    (hk : Nat.card {x : F // σ x = x} = q) :
    ∃ f : Multiplicative F →* residual σ hσ (n := n) r,
      Function.Injective f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨a, ha⟩ := exists_additive_embedding_three σ hσ h2 q hc hk
  let f := (complementInCentralizer σ hσ (n := 3 + k)).comp
    ((left σ hσ (m := 3) (n := k)).comp a)
  have hf : Function.Injective f := (complementInCentralizer_injective σ hσ).comp
    ((left_injective σ hσ).comp ha)
  have hm (x : Multiplicative F) : f x ∈ residual σ hσ (n := 3 + k) r := by
    apply Subgroup.mem_primeToResidual_of_pow (n := 1)
    simp only [pow_one, ← map_pow, additive_pow, map_one]
  exact ⟨f.codRestrict _ hm, fun x y h => hf (congrArg Subtype.val h)⟩

/-- A subgroup of order `r^(2e)` and exponent dividing r in the actual residual.
The construction works for every odd defining prime, including r = 3. -/
theorem exists_elementary_subgroup_residual [Finite F] {r e n : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hn : 3 ≤ n)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e)) :
    ∃ A : Subgroup (residual σ hσ (n := n) r),
      IsElementaryAbelian r A ∧ Nat.card A = r ^ (2 * e) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (p := r) (f := e * 2) (by
    simpa only [← Nat.card_eq_fintype_card, pow_mul] using hc)
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff F r 2).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have := (Fact.out : r.Prime).two_le
    omega
  have hk := FiniteField.card_fixed_of_quadratic_frobenius σ r e he hc hj
  obtain ⟨f, hf⟩ := exists_additive_embedding_residual σ hσ (r := r) hn h2 (r ^ e) hc hk
  refine ⟨f.range, ?_, ?_⟩
  · refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    change f y ^ r = 1
    rw [← map_pow, additive_pow, map_one]
  · calc
      Nat.card f.range = Nat.card (Multiplicative F) :=
        (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
      _ = Nat.card F := Nat.card_congr Multiplicative.toAdd
      _ = r ^ (2 * e) := by simpa only [← pow_mul, Nat.mul_comm e 2] using hc

private instance residualRanks_finitePGL [Finite F] {d : ℕ} :
    Finite (ProjGenLinGroup (Fin d) F) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

/-- Defining rank at least twice the fixed-field exponent when the complement
has dimension at least three. -/
theorem two_mul_fieldExponent_le_residual [Finite F] {r e n : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hn : 3 ≤ n)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e)) :
    2 * e ≤ primeRank r (residual σ hσ (n := n) r) := by
  obtain ⟨A, hA, hcard⟩ := exists_elementary_subgroup_residual σ hσ hr he hn hc hj
  let : IsElementaryAbelian r A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply primeRank_ge_of_elementary_embedding (A := A) ?_ hcard A.subtype Subtype.val_injective
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p r A)

/-- The dimension and field restriction in the unitary branch of A.2.17,
derived from the defining-prime rank of the literal residual alone. -/
theorem dimension_restriction_of_residual_rank_le_one [Finite F]
    {r e n : ℕ} [Fact r.Prime] (hr : r ≠ 2) (he : 0 < e) (hn : 0 < n)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e))
    (hJ : primeRank r (residual σ hσ (n := n) r) ≤ 1) :
    n = 1 ∨ n = 2 ∧ e = 1 := by
  have hnlt : n < 3 := by
    by_contra h
    have hbound := two_mul_fieldExponent_le_residual σ hσ (n := n) hr he (by omega) hc hj
    omega
  rcases (show n = 1 ∨ n = 2 by omega) with h | rfl
  · exact Or.inl h
  · have hbound := fieldExponent_le_residual_two σ hσ hr he hc hj
    exact Or.inr ⟨rfl, by omega⟩

/-- Literal application of both bounds in (*) of A.2.17. In ambient dimension
`2+n`, only dimension three, or dimension four over the prime fixed field,
can remain. The defining-prime bound already suffices. -/
theorem dimension_restriction_of_residual_ranks_le_one [Finite F]
    {r e n : ℕ} [Fact r.Prime] (hr : r ≠ 2) (he : 0 < e) (hn : 0 < n)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e))
    (_h3 : primeRank 3 (residual σ hσ (n := n) r) ≤ 1)
    (hrank : primeRank r (residual σ hσ (n := n) r) ≤ 1) :
    2 + n = 3 ∨ 2 + n = 4 ∧ e = 1 := by
  have h := dimension_restriction_of_residual_rank_le_one σ hσ hr he hn hc hj hrank
  omega

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental
