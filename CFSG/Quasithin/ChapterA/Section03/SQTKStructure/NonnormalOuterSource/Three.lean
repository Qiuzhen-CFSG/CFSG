module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Rank
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Linear
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Unitary
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.LinearUnitary
public import Theory.SpecificGroups.Classical.BinarySmallThreeRankOuter
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.Divisibility
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Nonnormal signed-three components have abelian outer group

The actual covering calculations bound the component center by three.
A distinct commuting conjugate then forces three-rank at most one in the
literal central quotient. The explicit cubic matrices exclude a nontrivial
diagonal outer factor. Full linear or unitary automorphism coverage leaves
an abelian field–graph quotient. Perfect central descent transfers this to
the original component, retaining every scalar kernel.

Source: Aschbacher–Smith A.3.8(3), pp.45–46, and the outer-group inspection
in Proposition 1.3.4, p.510; GLS3, Theorem 2.5.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
open Chapter1.Section02
open Theory.SpecificGroups.Classical.BinarySmallThreeRankOuter
variable {G : Type*} [Group G] [Finite G]

private theorem center_card_le_of_common {B : Type*} [Group B] [Finite B]
    [IsQuasisimple B] (h : A36Common B) : Nat.card (center B) ≤ 3 := by
  have hF : fittingSubgroup B = center B := le_antisymm
    ((le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center) (le_sSup ⟨inferInstance, inferInstance⟩)
  have hR : solvableRadical B = center B := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance inferInstance)
  rcases h.2.2.1 with hh | hh
  · have he := hh.2.2
    rw [hF, hR, relIndex_self] at he
    omega
  · rw [hF] at hh
    rcases hh.2.2 with he | he <;> omega

private theorem core_eq_bot (hcore : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : IsComponent G B) : pCore 2 B = ⊥ := by
  rw [pCore_subnormal_eq_comap 2 hB.1, hcore, MonoidHom.comap_bot]
  exact B.subtype.ker_eq_bot_iff.mpr B.subtype_injective

/-- The binary linear branch, on the original component and quotient marking. -/
theorem linear_even_outer (hG : primeRank 3 G ≤ 2) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal)
    (n : ℕ) (hn : 1 ≤ n) (hmodel : ClassicalGroup.IsPSL (B ⧸ center B) 3 (2 ^ n)) :
    IsMulCommutative (MulAut.Outer B) := by
  let : IsQuasisimple B := hB.2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  have hc := center_card_le_of_common
    (OrdinarySource.a36_linear_even hcore B hB n hn F hF e).2
  have hr := (nonnormal_component_three_rank hG hB hc hnormal).2
  rw [primeRank_equiv 3 e] at hr
  let := linear_outer_isMulCommutative (by omega : 0 < n) hF hr
  exact MulAut.outer_isMulCommutative_of_centralQuotient e

/-- The binary unitary branch, with arbitrary stored Hermitian form. -/
theorem unitary_even_outer (hG : primeRank 3 G ≤ 2) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal)
    (n : ℕ) (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSU (B ⧸ center B) 3 (2 ^ n)) :
    IsMulCommutative (MulAut.Outer B) := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  have hc := center_card_le_of_common (OrdinarySource.a36_unitary_even B hB
    (core_eq_bot hcore hB) n hn F J hF hconj e).2
  have hr := (nonnormal_component_three_rank hG hB hc hnormal).2
  rw [primeRank_equiv 3 e] at hr
  let := unitary_outer_isCyclic J (by omega : 1 < n) hF hconj hr
  exact MulAut.outer_isMulCommutative_of_centralQuotient e

/-- The odd-prime linear branch. Cubic diagonal torsion contradicts the rank bound. -/
theorem linear_odd_outer (hG : primeRank 3 G ≤ 2)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (B ⧸ center B) 3 p) :
    IsMulCommutative (MulAut.Outer B) := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hc := center_card_le_of_common
    (OrdinarySource.a36_linear_odd_prime B hB p hp ho F hF e).2
  have hr := (nonnormal_component_three_rank hG hB hc hnormal).2
  rw [primeRank_equiv 3 e] at hr
  have hcop : Nat.Coprime 3 (Nat.card F - 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_projective_of_three_dvd hd
    omega
  have hcover := Matrix.PSL3.OuterSolvable.standard_eq_top_of_odd_prime_card
    F (Group.IsPerfect.not_isSolvable _) hp ho hF
  let := Matrix.PSL3.OuterSolvable.innerDiagonalOuter_normal_of_coverage F hcover
  let := Matrix.PSL3.OuterSolvable.outerDiagonalQuotient_isMulCommutative_of_coverage F hcover
  let j := (QuotientGroup.quotientMulEquivOfEq
    (Matrix.PSL3.OuterSolvable.innerDiagonalOuter_eq_bot_of_coprime F hcop)).trans
      QuotientGroup.quotientBot
  let : IsMulCommutative (MulAut.Outer PSL(3,F)) := ⟨⟨fun x y => j.symm.injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩⟩
  exact MulAut.outer_isMulCommutative_of_centralQuotient e

/-- The odd-prime unitary branch; the actual Frobenius and form are retained. -/
theorem unitary_odd_outer (hG : primeRank 3 G ≤ 2) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (B ⧸ center B) 3 p) :
    IsMulCommutative (MulAut.Outer B) := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hmodel
  have hc := center_card_le_of_common (OrdinarySource.a36_unitary_odd_prime B hB
    (core_eq_bot hcore hB) p hp ho F J hF hconj e).2
  have hr := (nonnormal_component_three_rank hG hB hc hnormal).2
  rw [primeRank_equiv 3 e] at hr
  have hcop : Nat.Coprime 3 (p + 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective_of_three_dvd
      J hp hF hconj hd
    omega
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    let : Fact p.Prime := ⟨hp⟩
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hconj)
  obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J p hF hfixed
  let I := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let eS := e.trans eJ
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup I) := eS.symm.isSimpleGroup
  have hcover := HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd
    I rfl hp ho hF hfixed
  let := I.unitaryOuterHom_range_normal_of_semilinear_coverage rfl hcover
  have hcyc := I.outer_mod_unitary_isCyclic_of_semilinear_coverage rfl hcover
  let j := (QuotientGroup.quotientMulEquivOfEq
    (I.unitaryOuterHom_range_eq_bot_of_coprime hconj hcop)).trans QuotientGroup.quotientBot
  let := j.isCyclic.mp hcyc
  exact MulAut.outer_isMulCommutative_of_centralQuotient eS

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
