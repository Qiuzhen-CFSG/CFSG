module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryUnitaryOvergroup
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryPanelDefect
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorComparisons
/-!
# Binary unitary kernel alternatives and original-cover comparisons

The complete source endpoint catalogue now gives (2B), or the actual
order-144 action on nine points. The exceptional branch includes the exact
index [V : U intersect K] = 2, a normal PSU₃(2) subgroup of index two, and
a regular normal elementary three-group of order nine. These subgroups
belong to the same faithful local permutation group.

The Chapter 12 applications preserve both original endpoint markings and
the full Borel. On the regular branch they instantiate the previously
proved SU₃ and PSU₃ cover comparisons at q = 2, including the scalar
projection and the original factor/root representative equations. The
linear first endpoint supplies its own kernel containment.

The order-144 exception is retained, not excluded. The earlier marked
finite quotient and split data still require their source producers;
minimal-configuration reduction, exhaustive rank-two row selection, and
all seven marked amalgam lifts remain with the source-recognition assembly.
Source: Fong--Seitz I (2A)--(2B), pp.7--9, (5B)--(5C), pp.25--26;
DGS Theorem D, p.224; Aschbacher--Smith F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

/-- The unresolved degree-nine action, with its actual kernel defect and normal subgroups. -/
@[expose] def BinaryUnitaryException : Prop :=
  Group.IsSolvable (localGroup Q split i) ∧ Nat.card (Panel Q i) = 9 ∧
    Nat.card (localGroup Q split i) = 144 ∧
    (LocalCover.radical Q split i).relIndex (simpleRemainder Q split i) = 2 ∧
    ¬ simpleRemainder Q split i ≤ localKernel Q i ∧
    (∃ A : Subgroup (localGroup Q split i), A.Normal ∧ Nat.card A = 72 ∧
      A.index = 2 ∧ ClassicalGroup.IsPSU A 3 2) ∧
    (∃ N : Subgroup (localGroup Q split i), N.Normal ∧ IsElementaryAbelian 3 N ∧
      Nat.card N = 9 ∧ ∀ x y : Panel Q i, ∃! a : N, (a : localGroup Q split i) • x = y)

private theorem regularity_or_exception_of_binary_action
    (hs : Group.IsSolvable (localGroup Q split i)) (hp : Nat.card (Panel Q i) = 9)
    (hg : Nat.card (localGroup Q split i) = 72 ∨ Nat.card (localGroup Q split i) = 144)
    (A : Subgroup (localGroup Q split i)) (hAn : A.Normal) (hAc : Nat.card A = 72)
    (hAmodel : ClassicalGroup.IsPSU A 3 2) :
    (simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i)) ∨
      BinaryUnitaryException Q split i := by
  rcases BinaryPanel.remainder_index_cases Q split i hp hg with ⟨hg,hi,hV⟩ | ⟨hg,hi,hV⟩
  · exact Or.inl ⟨hV,remainder_comap_of_containment Q e split i hV⟩
  · have hindex : A.index = 2 := by
      have he := A.index_mul_card
      rw [hAc,hg] at he
      omega
    let := hs
    exact Or.inr ⟨hs,hp,hg,hi,hV,⟨A,hAn,hAc,hindex,hAmodel⟩,
      BinaryPanel.regular_nine_of_solvable (localGroup_two_pretransitive Q split i) hp (panelBase Q i)⟩

variable [Finite (L i)] (T : Sylow 2 (L i))
  (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

include e h hT in
/-- Every source endpoint satisfies (2B), apart from this actual order-144 action. -/
theorem remainder_le_kernel_or_binary_unitary_exception :
    (simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i)) ∨
      BinaryUnitaryException Q split i := by
  rcases remainder_le_kernel_or_small_unitary Q e h split i T hT with hreg | hpsu | hsu
  · exact Or.inl hreg
  · obtain ⟨F,hF,hfin,J,hcard,hconjugate,⟨μ⟩⟩ := hpsu
    obtain ⟨hs,hp,hi,hn,ha⟩ := binary_projectiveUnitary_local Q e h split i T hT J hcard hconjugate μ
    apply regularity_or_exception_of_binary_action Q e split i hs hp
      (binary_projectiveUnitary_local_order Q e h split i T hT J hcard hconjugate μ)
      _ hn ha
    exact ⟨F,hF,hfin,J,hcard,hconjugate,⟨(MonoidHom.ofInjective hi).symm⟩⟩
  · obtain ⟨F,hF,hfin,J,hcard,hconjugate,⟨ν⟩⟩ := hsu
    obtain ⟨hs,hp,hi,hn,ha⟩ := binary_specialUnitary_local Q e h split i T hT J hcard hconjugate ν
    apply regularity_or_exception_of_binary_action Q e split i hs hp
      (binary_specialUnitary_local_order Q e h split i T hT J hcard hconjugate ν)
      _ hn ha
    exact ⟨F,hF,hfin,J,hcard,hconjugate,⟨(MonoidHom.ofInjective hi).symm⟩⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 pair satisfies both kernel containments, or has the order-144 exception. -/
theorem rankOne_global_regularity_or_binary_unitary_exception
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∨
      MarkedLocal.BinaryUnitaryException Q split 1 := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  rcases MarkedLocal.remainder_le_kernel_or_binary_unitary_exception Q e hf split 1 T₁ hT₁ with h1 | hs
  · refine Or.inl ?_
    intro i
    fin_cases i
    · have h0 := MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
      exact ⟨h0,MarkedLocal.remainder_comap_of_containment Q e split 0 h0⟩
    · exact h1
  · exact Or.inr hs
/-- The binary special-unitary cover comparison, or the exact order-144 exception. -/
theorem rankOne_global_binary_specialUnitary_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hc : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (ν : (R ⧸ pCore 2 R) ≃* J.specialSubgroup) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    ((∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i) ∧
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* J.specialSubgroup,
      ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸
          MarkedLocal.originalRadicalInClosure Q e split 1) ≃* J.specialSubgroup,
          (∀ r, J.specialToProjective (a r) = b (MarkedLocal.originalRootProjection Q e split 1 r)) ∧
          (∀ r, c (QuotientGroup.mk' _ (inclusion
            (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r) ∧
          (∀ l : R, c (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
            ν (QuotientGroup.mk' (pCore 2 R) l)) ∧
          (RootLocalCover.projection Q split 1).ker = center (rankOne Q split 1)) ∨
      MarkedLocal.BinaryUnitaryException Q split 1 := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  rcases D.rankOne_global_regularity_or_binary_unitary_exception
      h hmany hn hpsl d hTH Q e split with hreg | hex
  · exact Or.inl ⟨fun i => (hreg i).1,
      MarkedLocal.specialUnitary_factor_comparison Q e hf split 1 T₁ hT₁ J
        (by decide : 0 < 1) hc hconj (hreg 1).1 ν⟩
  · exact Or.inr hex

/-- The binary projective-unitary cover comparison, or the exact order-144 exception. -/
theorem rankOne_global_binary_projectiveUnitary_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hc : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (μ : (R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    ((∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i) ∧
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸
          MarkedLocal.originalRadicalInClosure Q e split 1) ≃* ProjectiveSpecialUnitaryMatrixGroup J,
          (∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r)) ∧
          (∀ r, c (QuotientGroup.mk' _ (inclusion
            (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r) ∧
          (∀ l : R, c (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
            μ (QuotientGroup.mk' (pCore 2 R) l))) ∨
      MarkedLocal.BinaryUnitaryException Q split 1 := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  rcases D.rankOne_global_regularity_or_binary_unitary_exception
      h hmany hn hpsl d hTH Q e split with hreg | hex
  · exact Or.inl ⟨fun i => (hreg i).1,
      MarkedLocal.projectiveUnitary_factor_comparison Q e hf split 1 T₁ hT₁ J
        (by decide : 0 < 1) hc hconj (hreg 1).1 μ⟩
  · exact Or.inr hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
