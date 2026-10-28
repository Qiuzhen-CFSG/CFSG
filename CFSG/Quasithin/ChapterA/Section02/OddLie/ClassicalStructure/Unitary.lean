module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.ResidualSetup
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.ResidualRanks

/-!
# The unitary fundamental subgroup in A.2.17

For every stored Hermitian model of PSU in dimension 2+n, n>0, the genuine
SL₂ over its fixed field embeds properly and commutes with a faithfully embedded
complementary SU_n. Its central involution survives projectivization, and the
root subgroup witnesses the defining exponent in the involution centralizer.

In dimension four the complementary SU₂ lies in the actual prime-to-r residual
of the fundamental centralizer, even at q=3. Consequently residual r-rank at
most one forces e=1.

The standard-form source consumer below identifies the residual in all positive
complementary dimensions and supplies the elementary-abelian witness excluding
complementary dimension at least three under the source rank bounds; the first
theorem supplies the corresponding transport to every stored Hermitian model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.2.17, printed pp.38–39 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] [Finite F]
local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

/-- The source fundamental subgroup, complement, and local defining-rank witness
in every stored Hermitian model, with the actual fixed field retained. -/
theorem unitary_fundamental {n r e : ℕ} [NeZero n] [Fact r.Prime]
    (J : HermitianForm (2+n) F) (hr : r ≠ 2) (he : 0 < e)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, J.conj x = x ^ (r ^ e)) :
    ∃ (f : SpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj) →*
        ProjectiveSpecialUnitaryMatrixGroup J)
      (c : (form J.conj J.conj_involutive n).specialSubgroup →*
        ProjectiveSpecialUnitaryMatrixGroup J),
      Function.Injective f ∧ f.range ≠ ⊤ ∧ Function.Injective c ∧
      (∀ a b, Commute (f a) (c b)) ∧
      f (-1) ≠ 1 ∧ f (-1) ^ 2 = 1 ∧
      e ≤ primeRank r (Subgroup.centralizer ({f (-1)} :
        Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let : Finite (ProjGenLinGroup (Fin (2+n)) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hq : IsPrimePow (r ^ e) := (isPrimePow_nat_iff _).mpr
    ⟨r, e, Fact.out, he, rfl⟩
  have ho : Odd (r ^ e) := ((Fact.out : r.Prime).odd_of_ne_two hr).pow
  obtain ⟨f, c, hf, hp, hi, hcomm⟩ := exists_fundamental_complement J hq ho hc hj
  have hk : Nat.card (FixedBy.subfield F J.conj) = r ^ e :=
    J.fixed_card_prime_power hq hc hj
  let : Fintype (FixedBy.subfield F J.conj) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F J.conj) r := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hk)
  have hz := SpecialLinearGroup.map_neg_one_isInvolution hr f hf
  exact ⟨f, c, hf, hp, hi, hcomm, hz.1, hz.2,
    SpecialLinearGroup.fieldExponent_le_primeRank_centralizer hk f hf⟩

/-- In degree four the rank of the actual residual forces q to be prime. -/
theorem unitary_four_exponent_eq_one (σ : F ≃+* F) (hσ : Function.Involutive σ)
    {r e : ℕ} [Fact r.Prime] (hr : r ≠ 2) (he : 0 < e)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e))
    (hJ : primeRank r (residual σ hσ (n := 2) r) ≤ 1) : e = 1 := by
  have h := fieldExponent_le_residual_two σ hσ hr he hc hj
  omega

/-! ### The complete standard-form source consumer

The preceding theorem transports the two marked factors to an arbitrary stored
Hermitian form.  The following theorem keeps the identity-Gram model visible,
so that the literal centralizer residual from A.2.17 can be identified with the
complementary special-unitary group before any rank transport is performed.
-/

theorem unitary_standard_structure (σ : F ≃+* F) (hσ : Function.Involutive σ)
    {n r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hn : 0 < n)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e)) :
    ∃ (f : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) →*
        ProjectiveSpecialUnitaryMatrixGroup (form σ hσ (2 + n)))
      (c : (form σ hσ n).specialSubgroup →*
        ProjectiveSpecialUnitaryMatrixGroup (form σ hσ (2 + n))),
      Function.Injective f ∧ f.range ≠ ⊤ ∧ Function.Injective c ∧
      (∀ a b, Commute (f a) (c b)) ∧
      f.range = (projectLeft σ hσ (n := n)).range ∧
      f (-1) ≠ 1 ∧ f (-1) ^ 2 = 1 ∧
      e ≤ primeRank r (Subgroup.centralizer ({f (-1)} : Set
        (ProjectiveSpecialUnitaryMatrixGroup (form σ hσ (2 + n))))) ∧
      residual σ hσ (n := n) r =
        (complementInCentralizer σ hσ (n := n)).range ∧
      ∃ j : residual σ hσ (n := n) r ≃*
          (form σ hσ n).specialSubgroup,
        (∀ b, (j.symm b).val = complementInCentralizer σ hσ b) ∧
        primeRank r (residual σ hσ (n := n) r) =
          primeRank r (form σ hσ n).specialSubgroup := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hq : IsPrimePow (r ^ e) := (isPrimePow_nat_iff _).mpr
    ⟨r, e, Fact.out, he, rfl⟩
  have ho : Odd (r ^ e) := ((Fact.out : r.Prime).odd_of_ne_two hr).pow
  obtain ⟨a⟩ := nonempty_specialTwoEquiv_odd σ hσ hq ho hc hj
  let f := (projectLeft σ hσ (n := n)).comp a.symm.toMonoidHom
  let c := projectRight σ hσ (m := 2) (n := n)
  have hf : Function.Injective f :=
    (projectLeft_injective σ hσ).comp a.symm.injective
  have hc' : Function.Injective c := projectRight_injective σ hσ
  have hfrange : f.range = (projectLeft σ hσ (n := n)).range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨a.symm x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := a.symm.surjective x
      refine ⟨y, ?_⟩
      exact congrArg (fun z => projectLeft σ hσ z) hy
  have hproper : f.range ≠ ⊤ := by
    intro htop
    apply projectLeft_range_ne_top σ hσ (n := n)
    apply top_unique
    intro x _
    have hx : x ∈ f.range := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy⟩ := hx
    exact ⟨a.symm y, by simpa [f] using hy⟩
  have hcomm : ∀ x y, Commute (f x) (c y) := by
    intro x y
    exact factors_commute σ hσ (a.symm x) y
  have hk : Nat.card (FixedBy.subfield F σ) = r ^ e :=
    (form σ hσ 2).fixed_card_prime_power hq hc hj
  let : Fintype (FixedBy.subfield F σ) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F σ) r := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hk)
  let : Finite (ProjGenLinGroup (Fin (2 + n)) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hz := SpecialLinearGroup.map_neg_one_isInvolution hr f hf
  have hrank := SpecialLinearGroup.fieldExponent_le_primeRank_centralizer
    hk f hf
  have hres := residual_eq_complement σ hσ hr he hc hj hn
  have hje : ∃ j : residual σ hσ (n := n) r ≃*
      (form σ hσ n).specialSubgroup,
      (∀ b, (j.symm b).val = complementInCentralizer σ hσ b) ∧
      primeRank r (residual σ hσ (n := n) r) =
        primeRank r (form σ hσ n).specialSubgroup := by
    let j := residualEquiv σ hσ hr he hc hj hn
    refine ⟨j, ?_, ?_⟩
    · intro b
      exact residualEquiv_symm_coe σ hσ hr he hc hj hn b
    · exact primeRank_residual σ hσ hr he hc hj hn r
  exact ⟨f, c, hf, hproper, hc', hcomm, hfrange, hz.1, hz.2, hrank, hres, hje⟩

/-- The source rank bounds leave only the three-dimensional unitary case, or
the four-dimensional case over the prime field.  The residual is the literal
one attached to the displayed fundamental subgroup. -/
theorem unitary_dimension_restriction (σ : F ≃+* F) (hσ : Function.Involutive σ)
    {n r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hn : 0 < n)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e))
    (h3 : primeRank 3 (residual σ hσ (n := n) r) ≤ 1)
    (hrank : primeRank r (residual σ hσ (n := n) r) ≤ 1) :
    2 + n = 3 ∨ 2 + n = 4 ∧ e = 1 := by
  exact dimension_restriction_of_residual_ranks_le_one σ hσ hr he hn hc hj h3 hrank

/-- The concrete defining-prime witness used in the dimension argument.  It is
the additive subgroup in the complementary SU₃, extended by an identity block
and then placed in the actual projective residual. -/
theorem unitary_defining_rank_witness (σ : F ≃+* F)
    (hσ : Function.Involutive σ) {n r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hn : 3 ≤ n)
    (hc : Nat.card F = (r ^ e) ^ 2) (hj : ∀ x, σ x = x ^ (r ^ e)) :
    ∃ A : Subgroup (residual σ hσ (n := n) r),
      IsElementaryAbelian r A ∧ Nat.card A = r ^ (2 * e) :=
  exists_elementary_subgroup_residual σ hσ hr he hn hc hj

end CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure
