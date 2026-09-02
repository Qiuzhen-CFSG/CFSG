module

public import Stellmacher.LaterDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- The decomposition asserted in (8.1), presented through an explicit
quotient witness for `\bar G_a = G_a/C_{G_a}(Z_a)`.  The use of `Fin r`
records that the displayed direct products are finite products. -/
public structure LemmaEightOneConclusion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) : Prop where
  quotient_index:
    QuotientCardEqual
      (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a' ⊓ QAt ctx.Γ ctx.criticalPath.a)
  barred_decomposition:
    ∃ w : QuotientModuleWitness
        (GAt ctx.Γ ctx.criticalPath.a)
        (GAt ctx.Γ ctx.criticalPath.a ⊓
          Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
        (ZAt ctx.Γ ctx.criticalPath.a),
      let _ := w.groupX
      let _ := w.finiteX
      ∃ r : ℕ,
        ∃ Ebar : Fin r → Subgroup w.X,
        ∃ Elift : Fin r → Subgroup (GAt ctx.Γ ctx.criticalPath.a),
        ∃ V : Fin r → Subgroup H,
        ∃ V0 : Subgroup H,
        ∃ Jbar : Subgroup w.X,
        ∃ Jlift : Subgroup (GAt ctx.Γ ctx.criticalPath.a),
          let Zbar :=
            ZAt ctx.Γ ctx.criticalPath.a
          let EbarA :=
            ((EAt ctx.Γ ctx.criticalPath.a).subgroupOf
                (GAt ctx.Γ ctx.criticalPath.a)).map w.projection ⊔ Jbar
          let Rbar :=
            ⁅Zbar, ZAt ctx.Γ ctx.criticalPath.a'⁆
          Jbar = Jlift.map w.projection ∧
          Jlift.map (GAt ctx.Γ ctx.criticalPath.a).subtype =
            LocalJ Zbar (S : Subgroup H) ∧
          (∀ i : Fin r,
            Ebar i = (Elift i).map w.projection ∧
              V i = ⁅Zbar, (Elift i).map
                (GAt ctx.Γ ctx.criticalPath.a).subtype⁆) ∧
          EbarA = ⨆ i : Fin r, Ebar i ∧
          IsInternalDirectProductFamily EbarA Ebar ∧
          (∀ i : Fin r, IsModel (Ebar i) SL2Two) ∧
          Zbar = V0 ⊔ (⨆ i : Fin r, V i) ∧
          IsInternalDirectProductFamily Zbar
            (fun o : Option (Fin r) =>
              match o with | none => V0 | some i => V i) ∧
          V0 = Zbar ⊓ Subgroup.centralizer
            ((EAt ctx.Γ ctx.criticalPath.a ⊔
              Jlift.map (GAt ctx.Γ ctx.criticalPath.a).subtype :
                Subgroup H) : Set H) ∧
          (∀ i : Fin r, Nat.card (V i) = 4) ∧
          Rbar = ⨆ i : Fin r, (Rbar ⊓ V i) ∧
          IsInternalDirectProductFamily Rbar
            (fun i : Fin r => Rbar ⊓ V i)

/-- **Stellmacher (8.1).**  Under Hypothesis 2 and
`[Z_a,Z_{a'}] ≠ 1`, the two quotient indices are equal and the barred
`E_a J(Z_a,\bar S)` and `\bar Z_a` have the displayed direct-product
decompositions. -/
public theorem lemma_eight_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) :
    LemmaEightOneConclusion ctx := by
  sorry

end Stellmacher.SectionEight
