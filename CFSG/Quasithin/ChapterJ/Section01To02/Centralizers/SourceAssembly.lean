module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.LocalSource
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.OddPrimeCompletion
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicCompletion

/-!
# The remaining assembly boundary for J.2.7–10

All J.2.3 inputs, the Suzuki recognition and the odd-complement argument
are discharged here. J.2.9 and J.2.10 follow together from the precise
J.2.7(7),(8),(10) inputs below. Their producers must still construct the
small-model embedding and fusion, H-fusion, and the ambient Sylow witness.
These conditional deductions do not assert the unfinished J.2.7 clauses.

Source: Aschbacher–Smith, printed pp.435–438 (PDF pp.446–449).
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- J.2.9 and every clause of J.2.10, conditional only on the specified earlier J.2.7 data. -/
theorem suzuki_and_oddPrime_of_J27
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h*c.s*h⁻¹ = t)
    {t : G} (hst : IsConj c.s t)
    (f : Multiplicative (ZMod 2) × SuzukiMatrixGroup 0 →*
      centralizer ({t} : Set G)) (hf : Function.Injective f)
    (hzfusion : ∀ u : Multiplicative (ZMod 2) × SuzukiMatrixGroup 0,
      u.1 = 1 → orderOf u = 2 → IsConj c.z (f u : G)) :
    ∃ _r : c.SuzukiSourceConclusion,
      ∀ (p : ℕ) (_ : Fact p.Prime), p = 7 ∨ p = 13 → ∀ Y : Sylow p c.Ls,
        let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
        Nat.card YG = p ∧ (∃ S : Sylow p G, (S : Subgroup G) = YG) ∧
          normalizer (YG : Set G) ≤ normalizer (c.S0 : Set G) ∧
          centralizer (YG : Set G) = YG ⊔ c.S0 ∧
          IsCyclic YG.normalizerMonoidHom.range ∧
          Nat.card YG.normalizerMonoidHom.range = p - 1 := by
  let := c.S0_elementary_source
  obtain ⟨r⟩ := c.suzuki_recognition_of_J27 P hP hHs hsfusion hst f hf hzfusion
  exact ⟨r, fun p _ hp Y => r.oddPrime_source_conclusions c hp Y⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
