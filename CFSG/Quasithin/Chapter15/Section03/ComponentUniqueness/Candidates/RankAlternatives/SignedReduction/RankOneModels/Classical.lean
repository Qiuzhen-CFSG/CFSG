module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Classical exclusions in the rank-one paragraph of 15.3.37

The signed cubic witnesses force opposite field congruences in PSL₃ and PSU₃.
The actual PSL₄(2)–A₈ comparison and extension of linear maps exclude both
binary higher-dimensional groups. The nonabelian unipotent three-subgroup
excludes PSL₃(3). Perfectness supplied by quasisimplicity, together with the
projective-line Iwasawa structure, handles the two-core of the PSL₂ survivors
without adding parameter or simplicity assumptions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.1.5(3),
printed pp.501–503, and the first rank-one paragraph on p.1135.
The imported exceptional comparisons retain the ATLAS attribution and license
in `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.RankOneModels
variable {K : Type*} [Group K] [Finite K]

/-- A simple quasisimple group has trivial two-core. -/
theorem core_eq_bot_of_simple [IsQuasisimple K] [IsSimpleGroup K] : pCore 2 K = ⊥ := by
  rcases (inferInstance : (pCore 2 K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 K := (h ▸ pCore_isPGroup).of_equiv Subgroup.topEquiv
    let : Group.IsNilpotent K := hp.isNilpotent
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim

/-- Perfectness of the actual PSL₂ model suffices for its projective-line
simplicity theorem, including any small parameters allowed by the input. -/
theorem core_eq_bot_of_linear_two [IsQuasisimple K] {q : ℕ}
    (hmodel : ClassicalGroup.IsPSL K 2 q) : pCore 2 K = ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hmodel
  let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup PSL(2,F) := MulAction.IwasawaStructure.isSimpleGroup
    Group.IsPerfect.commutator_eq_top PSL2.Iwasawa inferInstance
  let : IsSimpleGroup K := e.isSimpleGroup
  exact core_eq_bot_of_simple

/-- Rank one forces the negative residue for the linear sign. -/
theorem linear_three_residue {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL K 3 (2 ^ n)) (hr : primeRank 3 K = 1) :
    2 ^ n % 3 = 2 := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  have hn : ¬ Even n := by
    intro hn
    have h := Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hc hn
    rw [← primeRank_equiv 3 e, hr] at h
    omega
  rw [Nat.BinaryTorusParity.two_pow_mod_three, if_neg (by simpa [Nat.even_iff] using hn)]

/-- The opposite linear parity has an elementary nine in the projective model. -/
theorem linear_three_even_rank {n : ℕ} (hn : Even n)
    (hmodel : ClassicalGroup.IsPSL K 3 (2 ^ n)) : 2 ≤ primeRank 3 K := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  rw [primeRank_equiv 3 e]
  exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hc hn

/-- Rank one forces the positive residue for the unitary sign. -/
theorem unitary_three_residue {n : ℕ} (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSU K 3 (2 ^ n)) (hr : primeRank 3 K = 1) :
    2 ^ n % 3 = 1 := by
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  have hne : ¬ Odd n := by
    intro ho
    have h := Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective J hn hc hconj ho
    rw [← primeRank_equiv 3 e, hr] at h
    omega
  rw [Nat.BinaryTorusParity.two_pow_mod_three, if_pos (by simpa [Nat.not_odd_iff_even,
    Nat.even_iff] using hne)]

private instance finiteLinear (n : ℕ) : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
  Finite.of_equiv SL(n, ZMod 2) (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv

private def fiveCoordinates : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2]
    ZMod 2 × (Fin 4 → ZMod 2) :=
  (LinearEquiv.piCongrLeft (ZMod 2) (fun _ : Option (Fin 4) => ZMod 2)
    (finSuccEquiv 4)).trans (LinearEquiv.piOptionEquivProd (ZMod 2))

private def extendFour : BinaryLinear.OuterCyclic.LinearGroup 4 →*
    BinaryLinear.OuterCyclic.LinearGroup 5 where
  toFun g := fiveCoordinates.trans
    (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr g).trans fiveCoordinates.symm)
  map_one' := by ext v i; simp [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]
  map_mul' g h := by ext v i; simp [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

private theorem extendFour_injective : Function.Injective extendFour := by
  intro g h he
  apply LinearEquiv.ext
  intro v
  have hh := congrArg (fun k : BinaryLinear.OuterCyclic.LinearGroup 5 =>
    (fiveCoordinates (k (fiveCoordinates.symm (0,v)))).2) he
  simpa [extendFour, LinearEquiv.trans_apply] using hh

private theorem binary_rank (n : ℕ) (hn : n = 4 ∨ n = 5) :
    2 ≤ primeRank 3 PSL(n, ZMod 2) := by
  have h4 : 2 ≤ primeRank 3 PSL(4, ZMod 2) := by
    rw [primeRank_equiv 3 Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  rcases hn with rfl | rfl
  · exact h4
  · rw [primeRank_equiv 3 (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))]
    rw [primeRank_equiv 3 (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))] at h4
    exact h4.trans (Theory.GroupTheory.primeRank_le_of_injective 3 extendFour extendFour_injective)

/-- The higher binary linear cases have rank at least two in their actual models. -/
theorem binary_linear_rank {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : ClassicalGroup.IsPSL K n 2) : 2 ≤ primeRank 3 K := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  rw [primeRank_equiv 3 (e.trans (Atlas.fieldEquivPSL n eF))]
  exact binary_rank n hn

/-- The ternary linear model contains the nonabelian unipotent three-group. -/
theorem linear_three_ternary_rank (hmodel : ClassicalGroup.IsPSL K 3 3) :
    2 ≤ primeRank 3 K := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  rw [primeRank_equiv 3 (e.trans (Atlas.fieldEquivPSL 3 eF))]
  let P := Matrix.PSL3Even.UnipotentGeometry.U (ZMod 3)
  let f := Matrix.PSL3Even.UnipotentGeometry.projective (ZMod 3)
  have hf := Matrix.PSL3Even.UnipotentGeometry.projective_injective (ZMod 3)
  have hp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by
    simpa [P] using Matrix.PSL3Even.UnipotentGeometry.card_U (ZMod 3))
  by_contra! hr
  have hP : primeRank 3 P ≤ 1 := (Theory.GroupTheory.primeRank_le_of_injective 3 f hf).trans (by omega)
  let : IsCyclic P := hp.isCyclic_of_odd_of_elementary_card_le (by decide) (by
    intro E hE
    let := hE
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hP E)
  have he := mul_comm (⟨1, 0, 0⟩ : P) ⟨0, 1, 0⟩
  have hh := (Matrix.PSL3Even.UnipotentGeometry.mul_comm_iff (ZMod 3) _ _).mp he
  norm_num at hh

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.RankOneModels
