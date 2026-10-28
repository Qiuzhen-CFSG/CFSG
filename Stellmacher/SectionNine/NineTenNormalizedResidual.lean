module

public import Stellmacher.SectionNine.NineTenNormalizedFactor
public import Stellmacher.SectionNine.NineResidualElementary

/-!
# The residual in the normalized terminal action

The constructed normalized transvection supplies a canonical factor in
the literal faithful action on terminal V/Z. In this same action range,
the image of the geometric terminal two-residual is the derived subgroup
of the full canonical factor product and is elementary abelian at three.
The normalized critical path, both explicit source noncontainments,
two-core kernel, and exact Section One hypotheses remain available.

Apply the actual local residual theorem at the normalized terminal and
its penultimate neighbor. That theorem obtains unique maximality and
Sylow supplementation from the genuine edge data, and uses the canonical
factor to eliminate the odd centralizer complement. The elementary-three
conclusion follows from the derived SL₂(2) product.

This supplies the residual identification in Stellmacher (9.10)(3),
printed p.57 of `refs/files/stellmacher-n-group.pdf`. The hypotheses
`Z_terminal ≰ V_first` and `Z_first ≰ V_terminal` are still explicit;
their unconditional production is the separate (9.8)/(9.9) work.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_residual_structure
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
      ∃ hN : ((ZAt ctx.Γ cp.a').subgroupOf (VAt ctx.Γ cp.a')).Normal,
        let _ := hN
        let P := GAt ctx.Γ cp.a'
        let U := VAt ctx.Γ cp.a'
        let Z := ZAt ctx.Γ cp.a'
        ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
          let _ := hW
          ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
            let X := action.range
            let W := U ⧸ Z.subgroupOf U
            let E := SectionOne.oneSevenGenerated (G := X) (V := W)
            let residual := ((EAt ctx.Γ cp.a').subgroupOf P).map action.rangeRestrict
            action.ker = pCore 2 P ∧
              SectionOne.Hypotheses X W ∧
              residual = (commutator E).map E.subtype ∧
              IsElementaryAbelian 3 residual := by
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, actor, _, _,
    hN, hW, action, _, hkernel, hyp, hcanonical⟩ :=
    nine_ten_normalized_first_factor ctx hb hterminalNot hfirstNot
  let _ := hN
  let _ := hW
  let normalizedCtx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    { ctx with criticalPath := cp, commutator_eq := hcomm }
  have hbound : 1 < normalizedCtx.criticalPath.length := by
    change 1 < cp.length
    rw [hlength]
    exact hb
  have hneighbor := (nine_three_initial_extraction_inputs normalizedCtx.toLocalContext hbound).1
  have hadj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor
  have hkernel' : pCore 2 (GAt ctx.Γ cp.a') ≤ action.rangeRestrict.ker :=
    ((MonoidHom.ker_rangeRestrict action).trans hkernel).symm.le
  have hresidual := nine_local_residual_eq_canonical_derived normalizedCtx.toLocalContext
    cp.a' _ hadj action.rangeRestrict action.rangeRestrict_surjective hkernel' hyp _ hcanonical
  have helementary := nine_local_residual_isElementaryAbelian_of_factor normalizedCtx.toLocalContext
    cp.a' _ hadj action.rangeRestrict action.rangeRestrict_surjective hkernel' hyp _ hcanonical
  exact ⟨cp, hlength, hcomm, hterminal, hfirst, hN, hW, action,
    hkernel, hyp, hresidual, helementary⟩

end Stellmacher.SectionNine
