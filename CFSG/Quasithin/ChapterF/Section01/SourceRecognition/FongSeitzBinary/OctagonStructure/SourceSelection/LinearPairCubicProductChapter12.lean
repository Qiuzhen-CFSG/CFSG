module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicStructureChapter12
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicProduct

/-!
# Chapter 12 application of the perpendicular product step

The selected two-linear octagon branch supplies the literal perpendicular
rank-one commutator.  With the actual local kernel containment and PSL₂
marking, `CubicProduct` turns that commutator into an internal multiplication
equivalence on the same marked quotient.  Both source orientations remain
explicit; this is the direct-product input for the later (6G) kernel
separation, not an exhaustive row-selection theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.LinearPanel
open ChapterF.Source.FongSeitzBinary.MarkedLocal
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open ChapterF.Source.FongSeitzBinary.ReeSource

variable {G X F₀ F₁ : Type*} [Group G] [Finite G] [Group X]
  [Field F₀] [Finite F₀] [CharP F₀ 2]
  [Field F₁] [Finite F₁] [CharP F₁ 2]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)

include D h hmany hn hpsl d hTH e split hm in
/-- The selected two-linear source branch carries its perpendicular product
through the actual rank-one marking in either degree orientation. -/
theorem rankOne_octagon_selected_linear_product
    (hK₀ : simpleRemainder Q split 0 ≤ localKernel Q 0)
    (μ₀ : localGroup Q split 0 ≃* PSL(2,F₀))
    (hK₁ : simpleRemainder Q split 1 ≤ localKernel Q 1)
    (μ₁ : localGroup Q split 1 ≃* PSL(2,F₁))
    (hbranch : ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) :
    ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n ∧
        ∃ z : rankOne Q split 0 ×
            rightConjugate (rankOne Q split 0)
              (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D) ≃*
            ↥(rankOne Q split 0 ⊔ rightConjugate (rankOne Q split 0)
              (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D)),
          ∀ a c, (z (a,c) : X ⧸ Q.D) = (a : X ⧸ Q.D) * (c : X ⧸ Q.D)) ∨
       (Odd b ∧ n = 2*b ∧
        ∃ z : rankOne Q split 1 ×
            rightConjugate (rankOne Q split 1)
              (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D) ≃*
            ↥(rankOne Q split 1 ⊔ rightConjugate (rankOne Q split 1)
              (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D)),
          ∀ a c, (z (a,c) : X ⧸ Q.D) = (a : X ⧸ Q.D) * (c : X ⧸ Q.D))) := by
  obtain ⟨b, hb, hR, hdata⟩ :=
    rankOne_octagon_selected_linear_cubic_structure D h hmany hn hpsl d hTH Q e split hm
      hbranch
  rcases hdata with ⟨ha, hratio, _, _, _, _, hcomm⟩ |
      ⟨hbodd, hratio, _, _, _, _, hcomm⟩
  · exact ⟨b, hb, hR, Or.inl ⟨ha, hratio,
      linear_commuting_product Q split 0 hK₀ μ₀
        (rightConjugate (rankOne Q split 0)
          (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D)) hcomm⟩⟩
  · exact ⟨b, hb, hR, Or.inr ⟨hbodd, hratio,
      linear_commuting_product Q split 1 hK₁ μ₁
        (rightConjugate (rankOne Q split 1)
          (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D)) hcomm⟩⟩

include D h hmany hn hpsl d hTH e split hm in
/-- The same marked two-linear branch determines the full perpendicular
Cartan product and separates its two endpoint panel kernels. -/
theorem rankOne_octagon_selected_linear_cartan_product
    (hK₀ : simpleRemainder Q split 0 ≤ localKernel Q 0)
    (μ₀ : localGroup Q split 0 ≃* PSL(2,F₀))
    (hK₁ : simpleRemainder Q split 1 ≤ localKernel Q 1)
    (μ₁ : localGroup Q split 1 ≃* PSL(2,F₁))
    (hbranch : ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) :
    ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n ∧
        ∃ z : F₀ˣ × F₀ˣ ≃* ↥((Q.tits.B ⊓ Q.tits.N) ⊓
            (rankOne Q split 0 ⊔ rightConjugate (rankOne Q split 0)
              (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D))),
          (∀ a c, (z (a,c) : X ⧸ Q.D) =
            alignedTorus Q split 0 hK₀ μ₀ (UnitarySource.actorReflection Q split 0) a *
              ((representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D)⁻¹ *
                alignedTorus Q split 0 hK₀ μ₀ (UnitarySource.actorReflection Q split 0) c *
                (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D))) ∧
          Nat.card ↥((Q.tits.B ⊓ Q.tits.N) ⊓
            (rankOne Q split 0 ⊔ rightConjugate (rankOne Q split 0)
              (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D))) =
            (Nat.card F₀ - 1)^2 ∧
          ((((Q.tits.B ⊓ Q.tits.N) ⊓
            (rankOne Q split 0 ⊔ rightConjugate (rankOne Q split 0)
              (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D))) ⊓
            embeddedPanelKernel Q 0) ⊓
              rightConjugate (embeddedPanelKernel Q 0)
                (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D) = ⊥)) ∨
       (Odd b ∧ n = 2*b ∧
        ∃ z : F₁ˣ × F₁ˣ ≃* ↥((Q.tits.B ⊓ Q.tits.N) ⊓
            (rankOne Q split 1 ⊔ rightConjugate (rankOne Q split 1)
              (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D))),
          (∀ a c, (z (a,c) : X ⧸ Q.D) =
            alignedTorus Q split 1 hK₁ μ₁ (UnitarySource.actorReflection Q split 1) a *
              ((representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D)⁻¹ *
                alignedTorus Q split 1 hK₁ μ₁ (UnitarySource.actorReflection Q split 1) c *
                (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D))) ∧
          Nat.card ↥((Q.tits.B ⊓ Q.tits.N) ⊓
            (rankOne Q split 1 ⊔ rightConjugate (rankOne Q split 1)
              (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D))) =
            (Nat.card F₁ - 1)^2 ∧
          ((((Q.tits.B ⊓ Q.tits.N) ⊓
            (rankOne Q split 1 ⊔ rightConjugate (rankOne Q split 1)
              (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D))) ⊓
            embeddedPanelKernel Q 1) ⊓
              rightConjugate (embeddedPanelKernel Q 1)
                (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D) = ⊥))) := by
  obtain ⟨b, hb, hR, hdata⟩ :=
    rankOne_octagon_selected_linear_cubic_structure D h hmany hn hpsl d hTH Q e split hm
      hbranch
  rcases hdata with ⟨hnodd, hratio, _, _, _, hcomm⟩ |
      ⟨hbodd, hratio, _, _, _, hcomm⟩
  · rcases hcomm with ⟨_, hcomm⟩
    obtain ⟨z, hz⟩ := perpendicular_linear_cartan_product Q split 0 hK₀ μ₀
      (Q.simple 1 * Q.simple 0 * Q.simple 1) hcomm
    exact ⟨b, hb, hR, Or.inl ⟨hnodd, hratio, z, hz,
      perpendicular_linear_cartan_card Q split 0 hK₀ μ₀
        (Q.simple 1 * Q.simple 0 * Q.simple 1) hcomm,
      perpendicular_linear_cartan_joint_kernel Q split 0 hK₀ μ₀
        (Q.simple 1 * Q.simple 0 * Q.simple 1) hcomm⟩⟩
  · rcases hcomm with ⟨_, hcomm⟩
    obtain ⟨z, hz⟩ := perpendicular_linear_cartan_product Q split 1 hK₁ μ₁
      (Q.simple 0 * Q.simple 1 * Q.simple 0) hcomm
    exact ⟨b, hb, hR, Or.inr ⟨hbodd, hratio, z, hz,
      perpendicular_linear_cartan_card Q split 1 hK₁ μ₁
        (Q.simple 0 * Q.simple 1 * Q.simple 0) hcomm,
      perpendicular_linear_cartan_joint_kernel Q split 1 hK₁ μ₁
        (Q.simple 0 * Q.simple 1 * Q.simple 0) hcomm⟩⟩

omit [Finite G] in
private theorem original_linear_local_marking
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (hf : HypothesisF11 ![L,R] (Global.sourceS L H))
    (split : SplitData Q.tits) (i : Fin 2)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (μ : ((![L,R] : Fin 2 → Subgroup G) i ⧸
      pCore 2 ((![L,R] : Fin 2 → Subgroup G) i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (localGroup Q split i ≃* PSL(2,F)) := by
  let := hf.finite_local i
  obtain ⟨T,hT⟩ := hf.sylow i
  have hK := MarkedLocal.linear_remainder_le_kernel Q e hf split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [MarkedLocal.simpleRoot_card_linear Q e hf split i T hT μ]
    exact ((Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center (((![L,R] : Fin 2 → Subgroup G) i) ⧸
      pCore 2 ((![L,R] : Fin 2 → Subgroup G) i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,F) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  exact ⟨hK,⟨(MarkedLocal.regularFactorLocalEquiv Q e hf split i T hT hK hc hz).trans μ⟩⟩

include D h hmany hn hpsl d hTH e split hm in
/-- The selected two-linear Chapter 12 branch constructs its perpendicular
rank-one product directly from the original F.1.1 factor quotients. The
local remainder containments and PSL₂ identifications are derived on the
same marked quotient; they are not extra model inputs. -/
theorem rankOne_octagon_selected_linear_product_of_original_factors
    (hbranch : ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) :
    ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n ∧
        ∃ z : rankOne Q split 0 ×
            rightConjugate (rankOne Q split 0)
              (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D) ≃*
            ↥(rankOne Q split 0 ⊔ rightConjugate (rankOne Q split 0)
              (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D)),
          ∀ a c, (z (a,c) : X ⧸ Q.D) = (a : X ⧸ Q.D) * (c : X ⧸ Q.D)) ∨
       (Odd b ∧ n = 2*b ∧
        ∃ z : rankOne Q split 1 ×
            rightConjugate (rankOne Q split 1)
              (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D) ≃*
            ↥(rankOne Q split 1 ⊔ rightConjugate (rankOne Q split 1)
              (representative (Q.simple 0 * Q.simple 1 * Q.simple 0) : X ⧸ Q.D)),
          ∀ a c, (z (a,c) : X ⧸ Q.D) = (a : X ⧸ Q.D) * (c : X ⧸ Q.D))) := by
  rcases hbranch with ⟨b,hb,hR,hratio⟩
  have hL0 : ClassicalGroup.IsPSL
      (((![L,R] : Fin 2 → Subgroup G) 0) ⧸
        pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) 2 (2^n) := by
    change ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)
    exact hpsl
  have hR1 : ClassicalGroup.IsPSL
      (((![L,R] : Fin 2 → Subgroup G) 1) ⧸
        pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) 2 (2^b) := by
    change ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b)
    exact hR
  obtain ⟨F₀,hF₀,hfin₀,hcard₀,⟨μ₀'⟩⟩ := hL0
  obtain ⟨F₁,hF₁,hfin₁,hcard₁,⟨μ₁'⟩⟩ := hR1
  let : Fintype F₀ := Fintype.ofFinite F₀
  let : Fintype F₁ := Fintype.ofFinite F₁
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
  let θ₀ : F₀ ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      hcard₀.trans (GaloisField.card 2 n (by omega)).symm)
  let θ₁ : F₁ ≃+* GaloisField 2 b := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      hcard₁.trans (GaloisField.card 2 b (by omega)).symm)
  let μ₀ : (((![L,R] : Fin 2 → Subgroup G) 0) ⧸
      pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) ≃*
      PSL2BinaryMatrixGroup n := μ₀'.trans (Atlas.fieldEquivPSL 2 θ₀)
  let μ₁ : (((![L,R] : Fin 2 → Subgroup G) 1) ⧸
      pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) ≃*
      PSL2BinaryMatrixGroup b := μ₁'.trans (Atlas.fieldEquivPSL 2 θ₁)
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨hK₀,⟨ν₀⟩⟩ := original_linear_local_marking Q e hf split 0 _ μ₀
  obtain ⟨hK₁,⟨ν₁⟩⟩ := original_linear_local_marking Q e hf split 1 _ μ₁
  exact rankOne_octagon_selected_linear_product D h hmany hn hpsl d hTH Q e split hm
    hK₀ ν₀ hK₁ ν₁ ⟨b,hb,hR,hratio⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
