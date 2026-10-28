module

public import Stellmacher.SectionNine.NineTenNormalizedCoatomData
public import Stellmacher.SectionNine.NineTenTransvectionCoatom

/-!
# A normalized transvection witness in (9.10)

The second extraction is first normalized so that its new vertex is the
initial vertex of a critical path. Criticality then supplies an element of
the initial center outside the terminal two-core. The centralizing coatom
argument makes its displacement on the terminal module an order-two
transvection modulo the terminal center.

This packages the first assertion after the normalization in Stellmacher
(9.10). The geometric extraction data remain available from
`nine_ten_normalized_coatom_data`; this result records the source's actual
transvection witness. Source: Stellmacher (9.10), printed p.57,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_transvection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot :
      ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot :
      ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ actor : G, actor ∈ ZAt ctx.Γ cp.a ∧ actor ∉ QAt ctx.Γ cp.a' ∧
        Nat.card (⁅VAt ctx.Γ cp.a', Subgroup.zpowers actor⁆ : Subgroup G) = 2 ∧
        QuotientCardEq
          (⁅VAt ctx.Γ cp.a', Subgroup.zpowers actor⁆ ⊔ ZAt ctx.Γ cp.a')
          (ZAt ctx.Γ cp.a') 2 := by
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, _, _, _, A0, _, _, _, hcoatom, hindex,
    hnotCore, _, _⟩ :=
    nine_ten_normalized_coatom_data ctx hb hterminalNot hfirstNot
  let normalizedCtx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    { ctx with criticalPath := cp, commutator_eq := hcomm }
  have hbound : 1 < normalizedCtx.criticalPath.length := by
    change 1 < cp.length
    rw [hlength]
    exact hb
  obtain ⟨actor, hactor, hactorNot⟩ := Set.not_subset.mp hnotCore
  change actor ∈ ZAt ctx.Γ cp.a at hactor
  change actor ∉ QAt ctx.Γ cp.a' at hactorNot
  have hfirstNorm :
      ¬ ZAt normalizedCtx.Γ normalizedCtx.criticalPath.firstStep ≤
        VAt normalizedCtx.Γ normalizedCtx.criticalPath.a' := by
    simpa only [normalizedCtx] using hfirst
  have hindexNorm : QuotientCardEq
      (VAt normalizedCtx.Γ normalizedCtx.criticalPath.a')
      (VAt normalizedCtx.Γ normalizedCtx.criticalPath.a' ⊓
        GAt normalizedCtx.Γ normalizedCtx.criticalPath.a) 2 := by
    simpa only [normalizedCtx, hcoatom] using hindex
  have hactorNorm : actor ∈ ZAt normalizedCtx.Γ normalizedCtx.criticalPath.a := by
    exact hactor
  have hactorNotNorm : actor ∉ QAt normalizedCtx.Γ normalizedCtx.criticalPath.a' := by
    exact hactorNot
  obtain ⟨hcard, hquotient⟩ := nine_ten_transvection_of_coatom normalizedCtx hbound
    hfirstNorm hindexNorm actor hactorNorm hactorNotNorm
  exact ⟨cp, hlength, hcomm, hterminal, hfirst, actor, hactor, hactorNot,
    by simpa only [normalizedCtx] using hcard,
    by simpa only [normalizedCtx] using hquotient⟩

end Stellmacher.SectionNine
