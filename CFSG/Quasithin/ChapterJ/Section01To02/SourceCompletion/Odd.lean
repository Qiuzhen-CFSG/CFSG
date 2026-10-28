module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.OddPrimeCompletion
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.Suzuki

/-!
# The original-source odd-prime normalizers

The constructed Suzuki centralizer and the elementary four-group S₀ discharge
the earlier-source inputs of the odd-complement argument. This gives J.2.10
on the literal image of each Sylow seven- or thirteen-subgroup of Lₛ.

Source: Aschbacher–Smith, J.2.10, printed p.438.
-/

public section
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Subgroup Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- All original J.2.10 clauses, with the Suzuki and S₀ inputs discharged. -/
theorem oddPrime_source {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13)
    (Y : Sylow p c.Ls) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    Nat.card YG = p ∧ (∃ S : Sylow p G, (S : Subgroup G) = YG) ∧
      normalizer (YG : Set G) ≤ normalizer (c.S0 : Set G) ∧
      centralizer (YG : Set G) = YG ⊔ c.S0 ∧
      IsCyclic YG.normalizerMonoidHom.range ∧
      Nat.card YG.normalizerMonoidHom.range = p - 1 := by
  let := c.S0_elementary_source
  obtain ⟨r⟩ := c.suzuki_source
  exact r.oddPrime_source_conclusions c hp Y

end CFSG.Quasithin.ChapterJ.SourceCompletion
