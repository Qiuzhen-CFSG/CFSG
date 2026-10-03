module

public import Stellmacher.SectionNine.NineEightIndexTwoContext
public import Stellmacher.SectionNine.LemmaNineSeven

/-!
# Stellmacher (9.8): terminal-center containment bounds the critical distance

If the terminal center lies in the first neighborhood module, the critical
distance is at most three. The geometric and local-action argument in
`NineEightIndexTwoContext` shows that a longer critical path would give a
transported context of the same length whose modules at offsets one and
three have intersection of index two. The actual ambient form of (9.7)
then forces that length to equal three. The original generated-subgroup
context is preserved as a wrapper around the ambient theorem.

Source: Stellmacher, Section 9, (9.8), printed pages 55–56.
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- Ambient form of Stellmacher (9.8), compatible with prescribed critical-pair
transport in the proof of the neighboring statements. -/
public theorem lemma_nine_eight_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ ctx.criticalPath.firstStep) :
    ctx.criticalPath.length ≤ 3 := by
  by_contra hnot
  have hb : 3 < ctx.criticalPath.length := by omega
  obtain ⟨shifted, hlength, third, hpath, hindex⟩ :=
    nine_eight_index_two_context ctx hb hcontain
  have hthree := (lemma_nine_seven_ambient shifted
    (by rw [hlength]; omega) third hpath hindex).1
  omega

/-- **Stellmacher (9.8).**  If `Z_{a'} ≤ V_{a+1}`, then the critical
distance is at most three. -/
public theorem lemma_nine_eight
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ ctx.criticalPath.firstStep) :
    ctx.criticalPath.length ≤ 3 :=
  lemma_nine_eight_ambient ctx.toAmbientContext hcontain

end Stellmacher.SectionNine
