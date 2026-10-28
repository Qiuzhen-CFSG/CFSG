module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Elementary C₂ geometry for the original Chapter12 selected factor

The original preparation for ![L,R] and S=O₂(N_G(L)∩H) supplies F.1.1.
Its complete marked amalgam isomorphism carries local characteristic two to
the finite quotient, so the same second-parabolic coset action is faithful.
The proved elementary Higman construction then applies to the original
quotient's orbit counts and literal U₂^{s₁} fixation.

The source counts and fixation, projective reconstruction, and final
symplectic model comparison remain unproved in this family. In particular,
this module does not assert ConcreteAmalgamComparison.symplectic or fill the
exhaustive comparison premise of the imported Chapter12 recognition core.

Source: Fong–Seitz II (7C), p.193; DGS Theorem D, p.224;
Aschbacher–Smith 5.2.6, pp.650–651 and Chapter12, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits)
local notation "Y" => ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D)
local notation "Ω" => C2RankThree.Points Q 1
local notation "a" => C2RankThree.rightCosetPoint Q 1 1
local notation "A₀" => MulAction.stabilizer Y a

include split in
/-- The literal Chapter12 selected factor supplies coset faithfulness from
its preparation, through the same quotient and both original markings. -/
theorem prepared_coset_faithful
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (i : Fin 2) : FaithfulSMul Y (C2RankThree.Points Q i) :=
  marked_coset_faithful Q (selectedFactorMarkedIso Q) (d.hypothesisF11 h hTH) split i

/-- Apply the elementary rank-three geometry to the original selected pair.
The actual source coset counts and U₂^{s₁} fixation remain to be established;
this does not yet construct ConcreteAmalgamComparison.symplectic. -/
theorem prepared_condition_i_lines
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    {q : ℕ} (hq : 2 ≤ q) (b c : Ω) (hab : a ≠ b)
    (t : Y) (hta : t • a = b) (htb : t • b = a)
    (hcov : MulAction.orbit A₀ c = (insert a (MulAction.orbit A₀ b))ᶜ)
    (hdegree : Nat.card Ω = q^3+q^2+q+1)
    (hsubdegree : Nat.card (MulAction.orbit A₀ b) = q*(q+1))
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hfix : ∀ u ∈ C2RankThree.kernelRoot Q split,
      ∀ c ∈ insert a (MulAction.orbit A₀ b), u • c = c) :
    ∃ D : PolarityDesign Ω q,
      (∀ x y, D.incident x y ↔ y = x ∨ (MulAction.SwappedOrbital.graph a b hab t hta htb).Adj x y) ∧
      D.block a = insert a (MulAction.orbit A₀ b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) :=
  marked_condition_i_lines Q (selectedFactorMarkedIso Q) (d.hypothesisF11 h hTH) split hq
    b c hab t hta htb hcov hdegree hsubdegree hq1 hfix

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
