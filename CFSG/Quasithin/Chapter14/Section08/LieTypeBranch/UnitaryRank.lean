module

public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer
public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer.BinaryForms
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.RankOneExclusion
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.UnitaryFive

/-!
# The complete unitary-family branch of Theorem D

A root involution and a faithfully projective norm-one three-torus exclude
all dimensions at least six. Genuine Hermitian basis changes cover every
form admitted by IsPSU. The actual PSU₂–PSL₂ comparison and the proved
rank-one Borel theorem exclude dimension two; the corresponding PSU₃
Borel theorem excludes dimension three. Dimension four is an allowed model.
The existing unitary-five torus theorem forces precisely n = 2 in dimension
five, and is reused here without an extra Levi or covering-group premise.

Thus a simple QTKE group with nonempty faithful local family and an actual
PSU_d(2^n) model, d ≥ 2 and n > 1, supplies the exact rank-two output at n.
The K-class remains arbitrary. Source: Aschbacher–Smith A.2.18 (printed p.40)
and Theorem D/14.8.2(1) (printed pp.1078–1079).
-/

public section

open BenderSuzuki.MatrixGroups HermitianForm.IdentityGram
open Theory.SpecificGroups.UnitaryRootNormalizer
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The root-normalizer obstruction bounds the actual unitary dimension. -/
theorem psu_degree_le_five_of_quasithin (hG : IsQuasithin G)
    {d n : ℕ} (hn : 0 < n) (hmodel : ClassicalGroup.IsPSU G d (2 ^ n)) : d ≤ 5 := by
  by_contra hlarge
  have hd : 6 ≤ d := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := charP_binary hn hcard
  obtain ⟨C, hC⟩ := exists_binary_identity_basis J hn hcard hconj
  let ep := e.trans (projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) :=
    Finite.of_injective ep.symm ep.symm.injective
  have hstd := Theory.GroupTheory.isQuasithin_of_equiv ep hG
  exact not_quasithin k (identityGram J) rfl hcard
    (Nat.one_lt_pow (by omega) (by decide))
    (even_two.pow_of_ne_zero (by omega)) hconj hstd

omit [Finite G] in
/-- The genuine PSU₂(2ⁿ) model is the PSL₂(2ⁿ) model over its actual fixed field. -/
theorem isPSL_two_of_isPSU_two {n : ℕ} (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSU G 2 (2 ^ n)) : ClassicalGroup.IsPSL G 2 (2 ^ n) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := charP_binary hn hcard
  have hc := fixed_card_binary J hn hcard hconj
  obtain ⟨ep⟩ := nonempty_projectiveTwoEquiv J hcard hc
  exact ⟨FixedBy.subfield F J.conj, inferInstance, inferInstance, hc, ⟨e.trans ep⟩⟩

/-- The actual faithful local family removes dimensions two and three;
quasithinness removes every dimension at least six. -/
theorem psu_degree_four_or_five_of_faithfulLocalComponents_nonempty
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSU G d (2 ^ n)) : d = 4 ∨ d = 5 := by
  have hle := psu_degree_le_five_of_quasithin h.quasithin (by omega) hmodel
  have h2 : d ≠ 2 := by
    rintro rfl
    exact hne.ne_empty (localFamilies_eq_empty_of_psl2 h T (by omega)
      (isPSL_two_of_isPSU_two (by omega) hmodel)).2
  have h3 : d ≠ 3 := by
    rintro rfl
    exact hne.ne_empty (localFamilies_eq_empty_of_psu3 h T (by omega) hmodel).2
  omega

/-- The complete unitary family supplies the rank-two model at the original exponent. -/
theorem rankTwoModel_of_psu
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSU G d (2 ^ n)) :
    ClassificationModels.IsRankTwoModel G n := by
  obtain rfl | rfl :=
    psu_degree_four_or_five_of_faithfulLocalComponents_nonempty h T hne hd hn hmodel
  · exact .unitary_four (by omega) hmodel
  · exact .unitary_five
      (psu_five_exponent_eq_two_of_quasithin h.quasithin (by omega) hmodel) hmodel

/-- The full Theorem D output for every simple-range binary unitary model with q > 2. -/
theorem theoremDModel_of_psu
    {K : GroupClass.{u}} (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSU G d (2 ^ n)) :
    ClassificationModels.IsTheoremDModel G :=
  .rank_two n hn (rankTwoModel_of_psu h T hne hd hn hmodel)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
