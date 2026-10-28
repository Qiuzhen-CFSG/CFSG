module
public import Stellmacher.SectionTen.TenOneMiddleCenterResidual
public import Theory.GroupTheory.NormalSixteenC4SquareRecognition
public import Stellmacher.SectionTen.TenOneMiddleResidualCard
public import Stellmacher.SectionTen.TenOneMiddleResidualOrderFour

/-!
# The middle residual core is C4 times C4

In the actual order-eight first-module case with local quotient SL2(2),
the middle residual two-core is isomorphic to C4×C4. No model, cardinality,
or order-four witness is supplied as an additional hypothesis.

The preceding producers give its order sixteen, an intrinsic center of
order at least four, and a genuine order-four element. Restrict this normal
core to the middle stabilizer. Actual initial-to-middle conjugation
transports the center-free stabilizer property from (7.5). The generic
normal-order-sixteen recognition then identifies the native core as C4×C4;
the subgroup inclusion equivalence transports that model back to the exact
ambient residual core.

Source: Stellmacher (10.1)(a1), printed p.60/PDF p.50, the middle residual
structure assertion following O₂(Emiddle)=[U,Emiddle],
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem recognition_of_order
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hcard : Nat.card (twoCoreIn (EAt ctx.Γ middle)) = 16)
    (hfour : ∃ x : twoCoreIn (EAt ctx.Γ middle), orderOf x = 4) :
    IsModel (twoCoreIn (EAt ctx.Γ middle)) (C4 × C4) := by
  let M := GAt ctx.Γ middle
  let Pa := GAt ctx.Γ ctx.criticalPath.a
  let E := EAt ctx.Γ middle
  let D := twoCoreIn E
  have hE : E = twoResidualIn M := ctx.Γ.twoResidualAt_def _
  have hEM : E ≤ M := hE ▸ twoResidualIn_le M
  have hDM : D ≤ M := (twoCoreIn_le E).trans hEM
  let N := D.subgroupOf M
  let _ : N.Normal := twoCoreIn_normal_of_normal E M hEM
    (hE ▸ twoResidualIn_normal M)
  obtain ⟨⟨actor,hactor⟩,_,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hPmap : Pa.map (MulAut.conj actor⁻¹).toMonoidHom = M :=
    (stabilizer_act ctx.Γ actor ctx.criticalPath.a).symm.trans (congrArg _ hactor)
  let eP : Pa ≃* M := ((MulAut.conj actor⁻¹).subgroupMap Pa).trans
    (MulEquiv.subgroupCongr hPmap)
  have hcenterM : Subgroup.center M = ⊥ := by
    apply Subgroup.card_eq_one.mp
    calc
      Nat.card (Subgroup.center M) = Nat.card (Subgroup.center Pa) :=
        (Nat.card_congr (Subgroup.centerCongr eP).toEquiv).symm
      _ = 1 := by
        rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).start_center_trivial,
          Subgroup.card_bot]
  let eD : N ≃* D := Subgroup.subgroupOfEquivOfLe hDM
  have hNcard : Nat.card N = 16 := (Nat.card_congr eD.toEquiv).trans hcard
  have hNcenter : 4 ≤ Nat.card (Subgroup.center N) := by
    rw [Nat.card_congr (Subgroup.centerCongr eD).toEquiv]
    exact ten_one_middle_residual_center_card ctx middle hpath
  have hNfour : ∃ x : N, orderOf x = 4 := by
    obtain ⟨x,hx⟩ := hfour
    refine ⟨eD.symm x, ?_⟩
    rw [eD.symm.orderOf_eq]
    exact hx
  obtain ⟨model⟩ := nonempty_mulEquiv_c4_square_of_normal_order_sixteen N
    hcenterM hNcard hNcenter hNfour
  exact ⟨eD.symm.trans model⟩
public theorem ten_one_middle_residual_c4_square
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    IsModel (twoCoreIn (EAt ctx.Γ middle)) (C4 × C4) := by
  have hcard := ten_one_middle_residual_core_card ctx middle hpath hsmall hmodel
  exact recognition_of_order ctx middle hpath hcard
    (ten_one_middle_residual_order_four ctx middle hpath hsmall hmodel hcard)
end Stellmacher.SectionTen
