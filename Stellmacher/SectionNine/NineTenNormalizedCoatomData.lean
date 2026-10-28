module

public import Stellmacher.SectionNine.NineTenNormalizedExtraction

/-!
# Normalized index-two coatom data in (9.10)

The normalized second extraction retains the exact index-two coatom in the
terminal module. The normalized critical initial center lies outside the
terminal two-core and normalizes that module by (7.4). This packages the
source-facing data before the separate coatom-centralization argument.

The geometric group and its residual conjugator remain in the returned data.
The separate coatom-centralization theorem uses the initial center of
order four, its first-step line of order two, and the source's explicit
first-center noncontainment. That centralization is not asserted here.

Source: Stellmacher (9.10), printed p.57, immediately before assertion (2).
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_coatom_data
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ (second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ cp.firstStep second
          (VAt ctx.Γ cp.a') E A0 actor),
        IsCriticalPathOffset ctx.Γ cp 2 second ∧
        ctx.Γ.act data.x⁻¹ second = cp.a ∧
        A0 = VAt ctx.Γ cp.a' ⊓ GAt ctx.Γ cp.a ∧
        QuotientCardEq (VAt ctx.Γ cp.a') A0 2 ∧
        (¬ ZAt ctx.Γ cp.a ≤ QAt ctx.Γ cp.a') ∧
        ZAt ctx.Γ cp.a ≤ GAt ctx.Γ cp.a' ∧
        ZAt ctx.Γ cp.a ≤ Subgroup.normalizer (VAt ctx.Γ cp.a' : Set G) := by
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, second, actor, E, A0, data,
    hsecond, hnew⟩ :=
    nine_ten_normalized_extraction ctx hb hterminalNot hfirstNot
  have hcoatom : A0 = VAt ctx.Γ cp.a' ⊓ GAt ctx.Γ cp.a := by
    simpa only [hnew] using data.coatom_eq
  have hindex : QuotientCardEq (VAt ctx.Γ cp.a') A0 2 := by
    change Nat.card (VAt ctx.Γ cp.a') = 2 * Nat.card A0
    exact data.coatom_card
  have hnotCore : ¬ ZAt ctx.Γ cp.a ≤ QAt ctx.Γ cp.a' := cp.critical.2
  have hcontain := lemma_seven_four ctx.sectionSeven ctx.Γ cp
  have hcenterTerminal : ZAt ctx.Γ cp.a ≤ GAt ctx.Γ cp.a' :=
    hcontain.first_containment.1.trans hcontain.first_containment.2
  have hnormal := hcenterTerminal.trans (stabilizer_le_normalizer_v ctx.Γ cp.a')
  exact ⟨cp, hlength, hcomm, hterminal, hfirst, second, actor, E, A0, data,
    hsecond, hnew, hcoatom, hindex, hnotCore, hcenterTerminal, hnormal⟩

end Stellmacher.SectionNine
