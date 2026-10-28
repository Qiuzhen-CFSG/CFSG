module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryScalarDerived
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryDerived

/-!
# Original unitary factors and the scalar-fixed derived section

The original linear and SU3/PSU3 quotient markings construct the same
scalar-fixed derived section and its faithful projective binary action.
The scalar center lies in the full Cartan three-core, and the section
contains the previously constructed full cubic radical centralizer.
The Frattini quotient has order at least 2^(6b), and at least 256 at b=1.
The actual projective map, full Borel and both endpoint squares are kept.

Source: Fong--Seitz I (6F), printed p.47. This supplies the literal
projective section, including the solvable degree-one case. The general
2^(8b) bound and subsequent commutator contradiction remain required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- Both original unitary conventions give the actual scalar-fixed derived
section, its cubic fixed subgroup and a faithful projective representation,
including degree one, with no extra representation hypothesis. -/
theorem original_linear_unitary_scalar_derived_projective
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∃ (hKj : simpleRemainder Q split j ≤ localKernel Q j)
      (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J),
      let d := unitaryScalarDerivedSection Q split j hKj
      rankOneScalar Q split j ≤ cartanThreeCore Q ∧
      simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤ d.numerator ∧
      d.action ≠ 1 ∧ d.effectiveAction.ker=(RootLocalCover.projection Q split j).ker ∧
      ∃ ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J)
          (Additive d.EffectiveCarrier),
        Function.Injective ρ ∧
        (∀ r, ρ (μ (RootLocalCover.projection Q split j r))=d.effectiveRepresentation r) ∧
        2^(6*b) ≤ Nat.card d.EffectiveCarrier ∧ (b=1 → 256 ≤ Nat.card d.EffectiveCarrier) := by
  have hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) := by
    rcases hmodel with hp | hs
    · exact Or.inl ⟨F,inferInstance,inferInstance,J,hcard,hconj,hp⟩
    · exact Or.inr ⟨F,inferInstance,inferInstance,J,hcard,hconj,hs⟩
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  obtain ⟨_,hab⟩ := original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj
  obtain ⟨E,hEfield,hEfin,hEcard,⟨ν⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  have hE2 : 2 < Nat.card E := by
    rw [hEcard,hab]
    exact (by decide : 2 < 2^2).trans_le
      (Nat.pow_le_pow_right (by decide) (show 2 ≤ 2*b by omega))
  have hregular := marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i ν
  let := h.finite_local j
  obtain ⟨Tj,hTj⟩ := h.sylow j
  obtain ⟨μ,σ,hσ,hsquare⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
    j (hregular j).1 hmodel.symm
  have hroot : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
    rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
    · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
    · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj ν
  have hsmall : b=1 → Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
    intro _
    rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
    · have hcj := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
        J hb hcard hconj ν
      exact Or.inr ⟨(regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hcj).trans ν⟩
    · have hcj := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j Tj hTj
        J hb hcard hconj ν
      exact Or.inl ⟨(regularFactorRootEquiv Q e h split j Tj hTj (hregular j).1 hcj).trans ν⟩
  obtain ⟨hZ,hmoving,hker,hrep⟩ := unitary_scalar_derived_projective Q split J hb hcard hconj
    hm i j hij (hregular j).1 μ σ hσ hsquare hroot hsmall (fun w => (hfixed w).2.1)
  refine ⟨(hregular j).1,μ,hZ,?_,hmoving,hker,hrep⟩
  have hdc := unitary_derived_threeCore_fixed Q split hm i j hij
    (fun w => (hfixed w).1) (fun w => (hfixed w).2.1)
    (unitary_rootFrattini_eq_commutator Q split J hb hcard hconj j (hregular j).1 μ)
  intro x hx
  exact ⟨(hdc.ge hx).1,centralizer_le hZ hx.2⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
