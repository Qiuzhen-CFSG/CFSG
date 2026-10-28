module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearRootCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.EffectiveSections

/-!
# Original and geometric Suzuki hexagon sections

Use the proved original-factor identification of the actual root-generated
R_j and its canonical root Sylow. The same quotient and amalgam marking
then carry effective actions on U_sj and Φ(U_sj), with the (4F) lower
bounds on their actual binary quotients. The two-layer bound gives
4(2m+1) ≤ 3a for the literal opposite root order 2^a.

This excludes opposite PSL₂(2) and PSL₂(4) endpoints against a nonsolvable
Suzuki actor. Only the acting factor has the perfectness hypothesis of
SuzukiLocalIdentification; the opposite factor needs none. The quotient
application uses Q.q, while the general marked application also covers
the universal geometric numerator without a descent assumption.

The nonlinear (2B) remainder-in-kernel premise remains explicit, with
its producer in split recognition. These results do not exclude Sz(2),
the larger mixed-parameter cases, or the equal-Suzuki case of (6C).

Source: Fong–Seitz I (4F), (5D)–(5F), (6C), printed pp.23–24,26–28,39–41;
DGS Theorem D, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

/-- Transport the actual original quotient Sylow to the canonical root.
This equivalence is used only for the invariant square property; no field
pinning or mixed-root equation is inferred from it. -/
def originalSuzukiRootEquiv (j : Fin 2) [Finite (L j)] (hp : Group.IsPerfect (L j))
    (T : Sylow 2 (L j)) (hT : (T : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) :
    simpleRoot Q split j ≃* SuzukiRootSubgroup m :=
  (MulEquiv.ofBijective (MarkedLocal.simpleRootSylowProjection Q e h split j hp T hT)
    ⟨MarkedLocal.simpleRootSylowProjection_injective Q e h split j hp T hT,
      MarkedLocal.suzuki_simpleRootSylowProjection_surjective Q e h split j hp T hT μ⟩).trans
    ((MarkedLocal.suzukiSylowEquiv j T μ).trans
      (((MarkedLocal.suzukiModelSylow j T μ).equiv (ReeSource.matrixRootSylow m)).trans
        (MulEquiv.subgroupCongr (ReeSource.matrixRootSylow_carrier m))))

/-- Nonlinear (5D)/(5F) and the two (4F) bounds on the same original or
geometric radical. The original perfect-factor identification discharges
the actual model and root-square inputs. Nonlinear (2B) is retained. -/
theorem effective_suzuki_radical_of_original_factor
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L j))
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ∃ d : RootSection Q split j,
      d.numerator = (MarkedLocal.sylowMap Q e h).range ⊓
        rightConjugate (MarkedLocal.sylowMap Q e h).range
          ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D) ∧
      d.denominator = ⊥ ∧ d.IsEffective ∧ Function.Injective d.effectiveRepresentation ∧
      (frattiniSection Q split j d).IsEffective ∧
      2^(4*(2*m+1)) ≤ Nat.card (d.numerator ⧸ frattini d.numerator) ∧
      2^(8*(2*m+1)) ≤ Nat.card d.numerator := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  let a := MarkedLocal.suzukiRankOneEquiv Q e h split j hp T hT μ
  let ν := originalSuzukiRootEquiv Q e h split j hp T hT μ
  have hpos := MarkedLocal.suzuki_parameter_pos j hp μ
  let s := UnitarySource.actorReflection Q split j
  let d := radicalSection Q split j hKj
  refine ⟨d, marked_radical_eq h Q e split j s.val s.class_eq, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact suzuki_radical_effective Q split j hpos a hm i hij s hKj
  · exact d.effectiveRepresentation_injective
      (suzuki_section_effectiveAction_injective Q split j hpos a d
        (suzuki_radical_action_ne_one Q split j hm i hij s hKj))
  · unfold RootSection.IsEffective
    rw [(MonoidHom.ker_eq_bot_iff _).mpr
      (suzuki_section_effectiveAction_injective Q split j hpos a _
        (suzuki_frattini_radical_action_ne_one Q split j hm i hij s hKj ν))]
    exact bot_le
  · exact suzuki_radical_card_bound Q split j hpos a hm i hij s hKj
  · exact suzuki_radical_two_layer_bound Q split j hpos a hm i hij s hKj ν

include e h in
/-- The source parameter restriction is on the actual opposite root order. -/
theorem original_suzuki_hexagon_parameter_bound
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L j))
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {a : ℕ} (hopp : Nat.card (simpleRoot Q split i) = 2^a) :
    4*(2*m+1) ≤ 3*a := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  exact suzuki_hexagon_parameter_bound Q split j
    (MarkedLocal.suzuki_parameter_pos j hp μ)
    (MarkedLocal.suzukiRankOneEquiv Q e h split j hp T hT μ)
    hm i hij (UnitarySource.actorReflection Q split j) hKj
    (originalSuzukiRootEquiv Q e h split j hp T hT μ) hopp

include e h in
/-- The binary and field-four opposite linear endpoints are genuinely
excluded against the nonsolvable Suzuki actor. No perfectness assumption
is made on the opposite original factor, including PSL₂(2). -/
theorem no_suzuki_hexagon_with_small_linear_opposite
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L j))
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hc := MarkedLocal.simpleRoot_card_linear Q e h split i T hT μi
  have hpos := MarkedLocal.suzuki_parameter_pos j hp μ
  rcases hF with hF | hF
  · have hh := original_suzuki_hexagon_parameter_bound Q e h split hm i j hij hp μ hKj
      (a := 1) (by norm_num [hF] at hc ⊢; exact hc)
    omega
  · have hh := original_suzuki_hexagon_parameter_bound Q e h split hm i j hij hp μ hKj
      (a := 2) (by norm_num [hF] at hc ⊢; exact hc)
    omega
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The same nonlinear effective sections under the literal original map Q.q. -/
theorem quotient_effective_suzuki_radical_of_original_factor
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L j))
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ∃ d : RootSection Q split j,
      d.numerator = ((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D) ∧
      d.denominator = ⊥ ∧ d.IsEffective ∧ Function.Injective d.effectiveRepresentation ∧
      (frattiniSection Q split j d).IsEffective ∧
      2^(4*(2*m+1)) ≤ Nat.card (d.numerator ⧸ frattini d.numerator) ∧
      2^(8*(2*m+1)) ≤ Nat.card d.numerator := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := effective_suzuki_radical_of_original_factor Q (originalMarkedIso Q) h split
    hm i j hij hp μ hKj
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

/-- The small-linear exclusion also applies to the original source quotient. -/
theorem quotient_no_suzuki_hexagon_with_small_linear_opposite
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L j))
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) : False :=
  no_suzuki_hexagon_with_small_linear_opposite Q (originalMarkedIso Q) h split
    hm i j hij hp μ μi hF hKj
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
