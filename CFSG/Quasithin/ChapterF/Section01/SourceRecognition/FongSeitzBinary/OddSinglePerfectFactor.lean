module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SylowGeneratedReduction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OddLinearRootCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# The odd source branch from one perfect endpoint

On an actual odd Weyl rotation, the source opposition element conjugates the
first canonical root to the second. A perfect first local factor therefore
places both canonical roots in the same two-residual. Ordered root generation
then puts U in that residual, and source Sylow generation makes the entire
marked quotient perfect. The first endpoint's original field coordinates
also parametrize every Weyl root and generate the same quotient without
assuming perfectness of the second endpoint.

The odd Weyl order remains an explicit source premise; it is not inferred
from a type label. This is a conditional reduction, not one of the seven
Fong–Seitz Lie comparisons. Source: Fong–Seitz I (1A), p.3; Carter
2.5.10–2.5.17; DGS, Groups and Graphs, Part II, pp.80–81 and Theorem D,
p.224. The source quotient, full Borel and both endpoint maps are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootGeneration
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h split

/-- One perfect first factor puts its simple root in the two-residual. -/
theorem first_simpleRoot_le_twoResidual_of_perfect
    (hp : Group.IsPerfect (L 0)) :
    simpleRoot Q split 0 ≤ pResidual 2 (X ⧸ Q.D) := by
  let := hp
  have hfactor : (factorMap Q e 0).range ≤ pResidual 2 (X ⧸ Q.D) := by
    let : Group.IsPerfect (factorMap Q e 0).range :=
      Group.IsPerfect.ofSurjective (factorMap Q e 0).rangeRestrict_surjective
    let : Group.IsNilpotent ((X ⧸ Q.D) ⧸ pResidual 2 (X ⧸ Q.D)) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_of_isPerfect_of_solvable_quotient _ _
  exact (simpleRoot_le_factor Q e h split 0 hp).trans hfactor

/-- Odd opposition and normal generation make the two-residual the whole quotient. -/
theorem twoResidual_eq_top_of_perfect_first_factor_of_odd
    (hp : Group.IsPerfect (L 0)) (hm : Odd (rotationOrder Q)) :
    pResidual 2 (X ⧸ Q.D) = ⊤ := by
  let R := pResidual 2 (X ⧸ Q.D)
  have hroot0 : simpleRoot Q split 0 ≤ R :=
    first_simpleRoot_le_twoResidual_of_perfect Q e h split hp
  have hroot1 : simpleRoot Q split 1 ≤ R := by
    rw [← simpleRoot_conjugate_of_odd Q split hm _ (representative_spec _)]
    intro x hx
    have hb : (representative (Q.simple 0 * longest Q) : X ⧸ Q.D) * x *
        (representative (Q.simple 0 * longest Q) : X ⧸ Q.D)⁻¹ ∈ R := hroot0 hx
    have hc := (inferInstance : R.Normal).conj_mem _ hb
      (representative (Q.simple 0 * longest Q) : X ⧸ Q.D)⁻¹
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc
  have hU : split.U ≤ R :=
    unipotent_le_normal_of_simpleRoots_le Q split R (by
      intro i
      fin_cases i
      · exact hroot0
      · exact hroot1)
  have hclosure : split.unipotentClosure ≤ R := by
    rw [split.unipotentClosure_eq_normalClosure]
    exact normalClosure_le_normal (fun _ hx => hU hx)
  apply top_unique
  rw [← unipotentClosure_eq_top_of_source Q e h split]
  exact hclosure

/-- One perfect endpoint makes the same odd-branch quotient perfect. -/
theorem quotient_isPerfect_of_perfect_first_factor_of_odd
    (hp : Group.IsPerfect (L 0)) (hm : Odd (rotationOrder Q)) :
    Group.IsPerfect (X ⧸ Q.D) := by
  let := twoResidual_isPerfect_of_source Q e h split
  let f := (MulEquiv.subgroupCongr
    (twoResidual_eq_top_of_perfect_first_factor_of_odd Q e h split hp hm)).trans
      Subgroup.topEquiv
  exact Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective

/-- The same odd-branch quotient is simple, with only the first endpoint
assumed perfect. -/
theorem quotient_isSimple_of_perfect_first_factor_of_odd
    (hp : Group.IsPerfect (L 0)) (hm : Odd (rotationOrder Q)) :
    IsSimpleGroup (X ⧸ Q.D) := by
  let := twoResidual_isSimple_of_perfect_factor Q e h split 0 hp
  let f := (MulEquiv.subgroupCongr
    (twoResidual_eq_top_of_perfect_first_factor_of_odd Q e h split hp hm)).trans
      Subgroup.topEquiv
  exact f.symm.isSimpleGroup

/-- The first-field root coordinates generate without perfectness of the second factor. -/
theorem oddWeylRootParameter_generate_of_source {F : Type*} [Field F] [Finite F]
    [CharP F 2] [Finite (L 0)] (hp : Group.IsPerfect (L 0))
    (hm : Odd (rotationOrder Q))
    (T : Sylow 2 (L 0)) (hT : (T : Subgroup (L 0)).map (L 0).subtype = S ⊓ L 0)
    (μ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,F)) :
    closure {g | ∃ j a, g = oddWeylRootParameter Q e h split hm hp T hT μ j a} = ⊤ := by
  apply root_parameters_generate_of_source Q e h split
  intro i w
  refine ⟨(i,w), ?_⟩
  rw [← oddWeylRootParameter_range Q e h split hm hp T hT μ (i,w)]
  exact Set.Subset.rfl

/-- The original first-factor field parametrizes every Weyl root on the same
odd source branch, and those parameters generate the whole quotient. -/
theorem exists_odd_linear_root_parameters_of_source
    (hp : Group.IsPerfect (L 0)) (hm : Odd (rotationOrder Q)) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2^n ∧
      ∃ x : (Fin 2 × Weyl Q) → Multiplicative K →* X ⧸ Q.D,
        (∀ j, (x j).range = rightConjugate (simpleRoot Q split j.1)
          (representative j.2 : X ⧸ Q.D)) ∧
        (∀ j, Function.Injective (x j)) ∧
        closure {g | ∃ j a, g = x j a} = ⊤ := by
  let := h.finite_local 0
  obtain ⟨K,hK,hf,hcard,⟨μ⟩⟩ := hmodel
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨T,hT⟩ := h.sylow 0
  exact ⟨K,hK,hf,inferInstance,hcard,
    oddWeylRootParameter Q e h split hm hp T hT μ,
    oddWeylRootParameter_range Q e h split hm hp T hT μ,
    oddWeylRootParameter_injective Q e h split hm hp T hT μ,
    oddWeylRootParameter_generate_of_source Q e h split hp hm T hT μ⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
