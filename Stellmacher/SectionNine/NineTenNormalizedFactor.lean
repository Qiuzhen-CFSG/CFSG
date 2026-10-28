module

public import Stellmacher.SectionNine.NineTenNormalizedTransvection
public import Stellmacher.SectionNine.NineNextTransvectionFactor

/-!
# The first canonical factor in (9.10)

The normalized transvection witness belongs to the terminal stabilizer by
(7.4). The faithful conjugation action on the terminal module modulo its
center has kernel equal to the terminal two-core. Its exact formula and
faithful Section One hypotheses are retained. The already proved
transvection-factor theorem then constructs a canonical (1.7) factor in
the literal action range.

This is the first factor used before assertions (3) and (4) in
Stellmacher (9.10), printed p.57 of `refs/files/stellmacher-n-group.pdf`.
The theorem retains the normalized path, both source noncontainments,
and the actual actor; it does not assert the full factor decomposition.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_first_factor
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
      ∃ actor : GAt ctx.Γ cp.a',
        (actor : G) ∈ ZAt ctx.Γ cp.a ∧
        (actor : G) ∉ QAt ctx.Γ cp.a' ∧
        ∃ hN : ((ZAt ctx.Γ cp.a').subgroupOf (VAt ctx.Γ cp.a')).Normal,
          let _ := hN
          let U := VAt ctx.Γ cp.a'
          let Z := ZAt ctx.Γ cp.a'
          ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
            let _ := hW
            ∃ action : GAt ctx.Γ cp.a' →* MulAut (U ⧸ Z.subgroupOf U),
              (∀ mover : GAt ctx.Γ cp.a', ∀ point : U,
                action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
                  QuotientGroup.mk' (Z.subgroupOf U)
                    ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                      (Subgroup.mem_normalizer_iff.mp
                        (stabilizer_le_normalizer_v ctx.Γ cp.a' mover.property) point).mp
                          point.property⟩) ∧
              action.ker = pCore 2 (GAt ctx.Γ cp.a') ∧
              SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U) ∧
              SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U)
                (⁅SectionOne.oddCore action.range,
                    Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
                  Subgroup.zpowers (action.rangeRestrict actor)) := by
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, actor, hactor, hactorNot,
    _, hindex⟩ := nine_ten_normalized_transvection ctx hb hterminalNot hfirstNot
  let normalizedCtx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    { ctx with criticalPath := cp, commutator_eq := hcomm }
  have hbound : 1 < normalizedCtx.criticalPath.length := by
    change 1 < cp.length
    rw [hlength]
    exact hb
  have hcontain := (lemma_seven_four ctx.sectionSeven ctx.Γ cp).first_containment
  have hactorP : actor ∈ GAt ctx.Γ cp.a' := hcontain.2 (hcontain.1 hactor)
  let actorP : GAt ctx.Γ cp.a' := ⟨actor, hactorP⟩
  obtain ⟨alignment, _, halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ cp hcomm
  have horbit : IsConjugateVertex ctx.Γ cp.firstStep cp.a' :=
    ⟨alignment, halign⟩
  have hfactor := nine_next_transvection_factor normalizedCtx hbound cp.a' horbit
    actorP hindex
  obtain ⟨hN, hW, action, hformula, hkernel, _, _, _, hyp, hcanonical⟩ := hfactor
  exact ⟨cp, hlength, hcomm, hterminal, hfirst, actorP, hactor, hactorNot,
    hN, hW, action, hformula, hkernel, hyp, hcanonical⟩

end Stellmacher.SectionNine
