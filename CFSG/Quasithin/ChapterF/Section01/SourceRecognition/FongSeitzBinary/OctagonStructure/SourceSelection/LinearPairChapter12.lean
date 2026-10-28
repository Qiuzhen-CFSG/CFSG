module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.Chapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairQuadraticDegrees
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearPanelCompletion

/-!
# The marked two-linear octagon input at Chapter 12

When the opposite endpoint selected by the original catalogue is linear, the
same finite-field identifications used by the source degree argument construct
both faithful endpoint panels.  This leaf packages the two full-Borel equations,
the two original endpoint squares and the literal factor maps together with the
quadratic degree ratio.  It is still a source input for the later (6G)
terminal argument; no ambient recognition is inferred from the parameter
calculation.

Source: Fong--Seitz I (1J)--(1K), (6G), pp.6--7,45--49; DGS Theorem D,
p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.LinearPanel
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open ChapterF.Source.FongSeitzBinary.ReeSource

private theorem binary_linear_marking {Y : Type*} [Group Y] {k : ℕ}
    (hk : 0 < k) (hlinear : ClassicalGroup.IsPSL Y 2 (2^k)) :
    Nonempty (Y ≃* PSL2BinaryMatrixGroup k) := by
  obtain ⟨F, hF, hfin, hcard, ⟨μ⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  let θ : F ≃+* GaloisField 2 k := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      hcard.trans (GaloisField.card 2 k hk.ne').symm)
  exact ⟨μ.trans (Atlas.fieldEquivPSL 2 θ)⟩

variable {G X : Type*} [Group G] [Finite G] [Group X]
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
/-- The two-linear octagon row carries both literal panel markings and the
quadratic field-degree alternative.  The endpoint maps are the same maps used
by the original factor quotients, so both Borel identities and both endpoint
squares remain available to the later source argument. -/
theorem rankOne_octagon_linear_pair_panel_data
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h0 : ClassicalGroup.IsPSL (((![L,R] : Fin 2 → Subgroup G) 0) ⧸ pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) 2 (2^a))
    (h1 : ClassicalGroup.IsPSL (((![L,R] : Fin 2 → Subgroup G) 1) ⧸ pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) 2 (2^b)) :
    ∃ (μ₀ : (((![L,R] : Fin 2 → Subgroup G) 0) ⧸ pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) ≃* PSL2BinaryMatrixGroup a)
      (μ₁ : (((![L,R] : Fin 2 → Subgroup G) 1) ⧸ pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) ≃* PSL2BinaryMatrixGroup b)
      (σ₀ : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup a)
      (T₀ : Sylow 2 (PSL2BinaryMatrixGroup a))
      (τ₀ : (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) 0 ⧸
        ReeSource.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 0) ≃*
        PSL2BinaryMatrixGroup a)
      (σ₁ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* PSL2BinaryMatrixGroup b)
      (T₁ : Sylow 2 (PSL2BinaryMatrixGroup b))
      (τ₁ : (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) 1 ⧸
        ReeSource.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1) ≃*
        PSL2BinaryMatrixGroup b),
      (quotientBorel Q 0).map σ₀.toMonoidHom = normalizer (T₀ : Set _) ∧
      (ReeSource.originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) 0).map
          τ₀.toMonoidHom = normalizer (T₀ : Set _) ∧
      (∀ x : parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) 0,
        τ₀ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := ![L,R])
          (S := Global.sourceS L H) 0) x) =
          σ₀ (QuotientGroup.mk' (panelKernel Q 0)
            (MarkedLocal.endpoint Q e 0 x))) ∧
      (rootProjection Q split 0).range.map σ₀.toMonoidHom = (T₀ : Subgroup _) ∧
      (∀ l : ((![L,R] : Fin 2 → Subgroup G) 0),
        τ₀ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := ![L,R])
          (S := Global.sourceS L H) 0)
        ⟨l, (show ((![L,R] : Fin 2 → Subgroup G) 0) ≤
            parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) 0 from
              le_sup_left.trans le_sup_left) l.property⟩) =
          μ₀ (QuotientGroup.mk' (pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) l)) ∧
      (quotientBorel Q 1).map σ₁.toMonoidHom = normalizer (T₁ : Set _) ∧
      (ReeSource.originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) 1).map
          τ₁.toMonoidHom = normalizer (T₁ : Set _) ∧
      (∀ x : parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) 1,
        τ₁ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := ![L,R])
          (S := Global.sourceS L H) 1) x) =
          σ₁ (QuotientGroup.mk' (panelKernel Q 1)
            (MarkedLocal.endpoint Q e 1 x))) ∧
      (rootProjection Q split 1).range.map σ₁.toMonoidHom = (T₁ : Subgroup _) ∧
      (∀ l : ((![L,R] : Fin 2 → Subgroup G) 1),
        τ₁ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := ![L,R])
          (S := Global.sourceS L H) 1)
        ⟨l, (show ((![L,R] : Fin 2 → Subgroup G) 1) ≤
            parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) 1 from
              le_sup_left.trans le_sup_left) l.property⟩) =
          μ₁ (QuotientGroup.mk' (pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) l)) ∧
      (Odd a ∧ b = 2*a ∨ Odd b ∧ a = 2*b) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨μ₀⟩ := binary_linear_marking ha h0
  obtain ⟨μ₁⟩ := binary_linear_marking hb h1
  obtain ⟨σ₀,T₀,τ₀,hσ₀,hτ₀,hsq₀,hroot₀,hfactor₀⟩ :=
    LinearPanel.original_panel Q e hf split 0 μ₀
  obtain ⟨σ₁,T₁,τ₁,hσ₁,hτ₁,hsq₁,hroot₁,hfactor₁⟩ :=
    LinearPanel.original_panel Q e hf split 1 μ₁
  have hratio := original_linear_factor_quadratic_degrees Q e hf split hm
    0 1 (by decide) ha hb h0 h1
  exact ⟨μ₀,μ₁,σ₀,T₀,τ₀,σ₁,T₁,τ₁,
    hσ₀,hτ₀,hsq₀,hroot₀,hfactor₀,
    hσ₁,hτ₁,hsq₁,hroot₁,hfactor₁,hratio⟩

include D h hmany hn hpsl d hTH e split hm in
/-- The source-selection disjunction now carries the literal factor squares
for its two-linear branch.  This is the Chapter 12 consumer of the full
panel construction; the Ree and unitary alternatives remain unchanged. -/
theorem rankOne_octagon_source_selection_with_linear_factor_squares :
    (∃ m, 0 < m ∧ Nonempty (OriginalReeSixHData Q e split n m)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
        ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b)) ∧
        ∃ (μ₀ : (((![L,R] : Fin 2 → Subgroup G) 0) ⧸
            pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) ≃*
            PSL2BinaryMatrixGroup n)
          (μ₁ : (((![L,R] : Fin 2 → Subgroup G) 1) ⧸
            pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) ≃*
            PSL2BinaryMatrixGroup b)
          (τ₀ : (parabolic (![L,R] : Fin 2 → Subgroup G)
            (Global.sourceS L H) 0 ⧸
              ReeSource.originalPanelKernel (L := ![L,R])
                (S := Global.sourceS L H) 0) ≃*
            PSL2BinaryMatrixGroup n)
          (τ₁ : (parabolic (![L,R] : Fin 2 → Subgroup G)
            (Global.sourceS L H) 1 ⧸
              ReeSource.originalPanelKernel (L := ![L,R])
                (S := Global.sourceS L H) 1) ≃*
            PSL2BinaryMatrixGroup b),
          (∀ l : ((![L,R] : Fin 2 → Subgroup G) 0),
            τ₀ (QuotientGroup.mk'
              (ReeSource.originalPanelKernel (L := ![L,R])
                (S := Global.sourceS L H) 0)
              ⟨l, (show ((![L,R] : Fin 2 → Subgroup G) 0) ≤
                parabolic (![L,R] : Fin 2 → Subgroup G)
                  (Global.sourceS L H) 0 from
                le_sup_left.trans le_sup_left) l.property⟩) =
              μ₀ (QuotientGroup.mk'
                (pCore 2 ((![L,R] : Fin 2 → Subgroup G) 0)) l)) ∧
          (∀ l : ((![L,R] : Fin 2 → Subgroup G) 1),
            τ₁ (QuotientGroup.mk'
              (ReeSource.originalPanelKernel (L := ![L,R])
                (S := Global.sourceS L H) 1)
              ⟨l, (show ((![L,R] : Fin 2 → Subgroup G) 1) ≤
                parabolic (![L,R] : Fin 2 → Subgroup G)
                  (Global.sourceS L H) 1 from
                le_sup_left.trans le_sup_left) l.property⟩) =
              μ₁ (QuotientGroup.mk'
                (pCore 2 ((![L,R] : Fin 2 → Subgroup G) 1)) l))) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) ∨
      (∃ b, 0 < b ∧ IsSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) := by
  obtain ⟨_, hrows⟩ := D.rankOne_octagon_source_selection h hmany hn hpsl d hTH Q e split hm
  rcases hrows with hree | hrows
  · exact Or.inl hree
  rcases hrows with hlin | hrows
  · rcases hlin with ⟨b, hb, hR, hratio⟩
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
    obtain ⟨μ₀, μ₁, _, _, τ₀, _, _, τ₁, hdata⟩ :=
      rankOne_octagon_linear_pair_panel_data D h hmany hn hpsl d hTH Q e split hm
        (a := n) (b := b) (by omega) hb hL0 hR1
    rcases hdata with ⟨_, _, _, _, hfactor₀, _, _, _, _, hfactor₁, _⟩
    exact Or.inr (Or.inl ⟨b, hb, hR, hratio, μ₀, μ₁, τ₀, τ₁,
      hfactor₀, hfactor₁⟩)
  · exact Or.inr (Or.inr hrows)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
