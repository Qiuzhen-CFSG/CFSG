module

public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph.Quotient
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph.Orthogonal
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.FieldTheory.Fixed

/-!
# Rank calculations for the outer-involution fixed-group models

The standard graph fixed group is the actual SL₂, whose Sylow two-subgroups
are additive copies of the field. A nontrivial field involution has fixed
field of degree one half of the original degree. The linear and unitary
rank calculations therefore give the required bounds after an actual
fixed-group identification. The unitary calculation uses the cardinality
of the stored involution's fixed field, without assuming that the involution
has already been written as Frobenius. All positive degrees, including one,
are retained.

The general conjugacy and descent identifications are separate obligations;
these conditional transport lemmas do not assert them. Source: GLS3,
Theorem 2.5.12 and §2.7; Aschbacher–Smith E.1.14(1), printed p.214,
and the involution types in 16.1.4, printed p.1171. The whole fixed groups,
not their two-residuals, occur throughout.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F] [Finite F]

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The exact fixed field of a nontrivial involution has half the binary degree. -/
theorem fixedField_parameters {f : ℕ} (_hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (σ : F ≃+* F) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ f = 2 * n ∧ Nat.card (FixedBy.subfield F σ) = 2 ^ n := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let H := Subgroup.zpowers σ
  let K := FixedPoints.subfield H F
  have ho : orderOf σ = 2 := orderOf_eq_prime hσ hne
  let : Finite H := Finite.of_injective
    (fun g : H => (g.val : F → F)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  have hd : Module.finrank K F = 2 := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers, ho]
  have hK : K = FixedBy.subfield F σ := by
    ext x
    change (∀ g : H, g • x = x) ↔ σ x = x
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, _, hn⟩ := FiniteField.card K 2
  have hcard : Nat.card F = 2 ^ (2 * (n : ℕ)) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hd, Nat.card_eq_fintype_card, hn,
      ← pow_mul, Nat.mul_comm]
  have hfn : f = 2 * (n : ℕ) :=
    Nat.pow_right_injective (by decide : 1 < 2) (hF.symm.trans hcard)
  refine ⟨n, n.pos, hfn, ?_⟩
  rw [← hK, Nat.card_eq_fintype_card, hn]

private theorem sl2_two_rank_le [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    primeRank 2 SL(2,F) ≤ f := by
  let P : Sylow 2 SL(2,F) := default
  rw [P.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro E _
  apply (Subgroup.card_le_card_group E).trans
  have hc : Nat.card P = Nat.card F :=
    (Nat.card_congr (SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv).symm
  exact (hc.trans hF).le

/-- The whole standard graph fixed group has two-rank at most the field degree. -/
theorem standard_graph_fixed_rank {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    primeRank 2 (graph F).fixedSubgroup ≤ f := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e := (Matrix.PSL3Four.GraphFixed.projectiveGraphFixedEquivSpecial F).trans
    (Matrix.PSL3Four.GraphFixed.graphSLFixedEquivSL2 F)
  rw [primeRank_equiv 2 e]
  exact sl2_two_rank_le hF

/-- Transport the standard graph calculation through an actual actor conjugacy. -/
theorem graph_fixed_rank_of_congr {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (a c : MulAut PSL(3,F)) (hc : MulAut.congr c a = graph F) :
    primeRank 2 a.fixedSubgroup ≤ f := by
  rw [primeRank_equiv 2 (MulAut.fixedSubgroupCongr c a), hc]
  exact standard_graph_fixed_rank hF

/-- Fixed-field descent to the actual smaller projective linear group gives
rank equal to the original field degree. The descent equivalence is explicit. -/
theorem field_fixed_rank_of_equiv {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (σ : F ≃+* F) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (e : a.fixedSubgroup ≃* PSL(3, FixedBy.subfield F σ)) :
    primeRank 2 a.fixedSubgroup = f := by
  obtain ⟨n, hn, hfn, hK⟩ := fixedField_parameters hf hF σ hσ hne
  rw [primeRank_equiv 2 e, Matrix.PSL3Even.two_rank _ hn hK, hfn]

/-- The unitary rank theorem with the actual fixed-field cardinality as input.
Standard-form transport retains the stored involution and the projective carrier. -/
theorem unitary_two_rank_of_fixed_card (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n) :
    primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) = n := by
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ n) hF hfixed
  rw [primeRank_equiv 2 e]
  exact HermitianForm.EvenTwoRank.standard_two_rank _ rfl hn hF hfixed

/-- An actual unitary fixed-group identification gives the sharper bound,
including the whole order-72 group at original degree two. -/
theorem graphField_fixed_rank_of_equiv {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (σ : F ≃+* F) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (J : HermitianForm 3 F) (hJ : J.conj = σ)
    (e : a.fixedSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    primeRank 2 a.fixedSubgroup ≤ f - 1 := by
  obtain ⟨n, hn, hfn, hK⟩ := fixedField_parameters hf hF σ hσ hne
  have hcard : Nat.card F = (2 ^ n) ^ 2 := by rw [hF, hfn, pow_mul']
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n := by
    rw [hJ]
    exact hK
  rw [primeRank_equiv 2 e, unitary_two_rank_of_fixed_card J hn hcard hfixed]
  omega

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks
