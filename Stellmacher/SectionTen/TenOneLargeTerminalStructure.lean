module
public import Stellmacher.SectionTen.TenOneLargeTerminalCardinalities
public import Stellmacher.SectionTen.TenOneLargeActionClassification
public import Stellmacher.SectionTen.TenOneLargeResidualGeneration
public import Stellmacher.SectionTen.TenOneLargeCyclicThreeExclusion
public import Stellmacher.SectionTen.TenOneLargeExtraspecialExclusion

/-!
# The large terminal residual alternatives in source (14)

For the actual Section Ten context and its offset-two middle vertex, assume
that no first-module actor outside the terminal core induces a transvection
on the terminal quotient. The image of the terminal residual in the literal
quotient P/O₂(P) is C₃×C₃ or C₅. The terminal module has order thirty-two,
and its intersection with the first module has order eight.

The proof constructs the actual terminal quotient-conjugation action and
selects the small-displacement actor from the proved geometric producer.
Source (13) identifies its canonical odd commutator with the entire residual
image and odd core. The actual specialization of (1.3) therefore applies to
this group. The cyclic-three exclusion and the extraspecial-normalizer
contradiction remove the other alternatives. Full residual support and the
fixed-displacement cardinality theorem then give the two module orders.
The first isomorphism theorem transports the surviving group models from
the action range to the residual image in P/O₂(P), retaining the literal
quotient rather than identifying the ambient residual with an odd group.

Source: Stellmacher (10.1), printed p.63, equation (14). The C₃×C₃ alternative
is retained here; its later exclusion occurs only after source (18).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u

private theorem quotient_image_equiv_action_image
    {P X : Type*} [Group P] [Group X]
    (N : Subgroup P) [N.Normal] (action : P →* X) (hkernel : action.ker = N)
    (E : Subgroup P) :
    Nonempty ((E.map (QuotientGroup.mk' N)) ≃* (E.map action.rangeRestrict)) := by
  let equiv : (P ⧸ N) ≃* action.range :=
    (QuotientGroup.quotientMulEquivOfEq hkernel.symm).trans
      (QuotientGroup.quotientKerEquivRange action)
  have hcomp : equiv.toMonoidHom.comp (QuotientGroup.mk' N) = action.rangeRestrict := by
    apply MonoidHom.ext
    intro actor
    change (QuotientGroup.quotientKerEquivRange action)
      ((QuotientGroup.quotientMulEquivOfEq hkernel.symm) (QuotientGroup.mk actor)) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hmap : (E.map (QuotientGroup.mk' N)).map equiv.toMonoidHom =
      E.map action.rangeRestrict := by
    rw [Subgroup.map_map,hcomp]
  exact ⟨((E.map (QuotientGroup.mk' N)).equivMapOfInjective
    equiv.toMonoidHom equiv.injective).trans (MulEquiv.subgroupCongr hmap)⟩

public theorem ten_one_large_terminal_structure
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    : let P := GAt ctx.Γ ctx.criticalPath.a'
      let Ebar := ((EAt ctx.Γ ctx.criticalPath.a').subgroupOf P).map
        (QuotientGroup.mk' (pCore 2 P))
      (Nonempty (Ebar ≃* (C3 × C3)) ∨ Nonempty (Ebar ≃* C5)) ∧
        Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 32 ∧
        Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
          VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8 := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let Ebar := (E.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halignment⟩
  let _ := hN
  let _ := hW
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let W := V ⧸ Z.subgroupOf V
  let O := SectionOne.oddCore action.range
  obtain ⟨element,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  obtain ⟨hindex,hselected⟩ := hcases.resolve_left (hno element hactor hout)
  let actor : P := ⟨element,
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 hactor⟩
  have hgen := ten_one_large_residual_generation ctx middle hpath actor hactor
    action hformula hkernel hout hindex hselected hno
  have hsource13 : SectionOne.involutionCommutator action.range (action.rangeRestrict actor) = O := by
    change ⁅O,Subgroup.zpowers (action.rangeRestrict actor)⁆ = O
    have hh := hgen.2.1
    rw [hgen.1] at hh
    exact hh.symm
  have hodd : (E.subgroupOf P).map action.rangeRestrict = O := hgen.1
  let modelEquiv : Ebar ≃* O :=
    (quotient_image_equiv_action_image (pCore 2 P) action hkernel (E.subgroupOf P)).some.trans
      (MulEquiv.subgroupCongr hodd)
  have hthree : Nat.card O ≠ 3 := ten_one_large_oddCore_card_ne_three
    ctx middle hpath hno action hformula hkernel
  have hnotThree : ¬ Nonempty (O ≃* Multiplicative (ZMod 3)) := by
    rintro ⟨e⟩
    apply hthree
    exact (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)).trans
        (by norm_num))
  have hclass := (ten_one_large_action_classification ctx action hformula hkernel
    actor hactor hout hindex).2.2
  change SectionOne.LemmaOneThreeConclusion action.range W
    (action.rangeRestrict actor)
    (SectionOne.involutionCommutator action.range (action.rangeRestrict actor)) at hclass
  rw [hsource13] at hclass
  cases hclass with
  | cyclicThree hcard hmodel => exact (hnotThree hmodel).elim
  | small hcard hfixed hmodels =>
    have hcards := ten_one_large_terminal_cardinalities ctx middle hpath hno
      action hformula hkernel hcard
    refine ⟨?_,hcards⟩
    rcases hmodels.resolve_left hnotThree with ⟨hfive⟩ | ⟨hthreeSquare⟩
    · exact Or.inr ⟨modelEquiv.trans hfive.some⟩
    · exact Or.inl ⟨modelEquiv.trans hthreeSquare.some⟩
  | extraspecial hcard hfixed hcenter hspecial horder =>
    exact (ten_one_large_extraspecial_alternative_impossible ctx middle hpath actor hactor
      action hformula hkernel hout hindex hselected hno hspecial horder hcenter).elim

end Stellmacher.SectionTen
