module

public import Stellmacher.SectionNine.NineFiveSupportData
public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer
public import Stellmacher.SectionFiveToSeven.Result7_6

/-!
# Geometric reductions for the quotient recognition in (9.5)

The lifted support has order eight. Its conjugator lies in the actual
terminal stabilizer, and equality of the two supports is equivalent to
the order-eight branch. The centralizer bound is transported to the
terminal vertex with the ambient hypotheses retained on H.
These reductions do not assert the quotient models.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem nine_five_support_card
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (prev : ctx.Γ.Vertex) (actor : G)
    (data : NineFiveSupportData ctx prev actor) :
    Nat.card data.support = 8 := by
  have hindex := data.support_index
  unfold QuotientCardEq at hindex
  simpa [data.center_card] using hindex

public theorem nine_five_support_equal_iff_card_eight
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (prev : ctx.Γ.Vertex) (actor : G)
    (data : NineFiveSupportData ctx prev actor) :
    data.support = data.support.map (MulAut.conj data.conjugator⁻¹).toMonoidHom ↔
      Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3 := by
  constructor
  · intro hequal
    rw [data.span, ← hequal, sup_idem, nine_five_support_card ctx prev actor data]
    norm_num
  · intro hcard
    have hfirst : data.support ≤ VAt ctx.Γ ctx.criticalPath.a' :=
      le_sup_left.trans_eq data.span.symm
    have hother : data.support.map (MulAut.conj data.conjugator⁻¹).toMonoidHom ≤
        VAt ctx.Γ ctx.criticalPath.a' := le_sup_right.trans_eq data.span.symm
    have hfirstEq := Subgroup.eq_of_le_of_card_ge hfirst (by
      rw [hcard, nine_five_support_card ctx prev actor data]
      norm_num)
    have hotherEq := Subgroup.eq_of_le_of_card_ge hother (by
      rw [hcard, Subgroup.card_map_of_injective (MulAut.conj data.conjugator⁻¹).injective,
        nine_five_support_card ctx prev actor data]
      norm_num)
    exact hfirstEq.trans hotherEq.symm

public theorem nine_five_support_distinct_iff_card_thirty_two
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (prev : ctx.Γ.Vertex) (actor : G)
    (data : NineFiveSupportData ctx prev actor) :
    data.support ≠ data.support.map (MulAut.conj data.conjugator⁻¹).toMonoidHom ↔
      Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 := by
  have hequal := nine_five_support_equal_iff_card_eight ctx prev actor data
  constructor
  · intro hne
    rcases nine_five_cardinalities_of_support ctx hb prev actor data with hsmall | hlarge
    · exact (hne (hequal.mpr hsmall)).elim
    · exact hlarge.1
  · intro hlarge heq
    have hsmall := hequal.mp heq
    norm_num at hsmall hlarge
    omega

public theorem nine_five_support_conjugator_mem_terminal
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (prev : ctx.Γ.Vertex) (actor : G)
    (data : NineFiveSupportData ctx prev actor) :
    data.conjugator ∈ GAt ctx.Γ ctx.criticalPath.a' := by
  let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hadj : ctx.Γ.adjacent penultimate ctx.criticalPath.a' := by
    have hedge := ctx.criticalPath.path_adj ⟨ctx.criticalPath.length - 1, by omega⟩
    have hend : (⟨ctx.criticalPath.length - 1, by omega⟩ :
        Fin ctx.criticalPath.length).succ =
        ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    simpa only [hend, ctx.criticalPath.path_end, Fin.castSucc_mk, penultimate] using hedge
  have hcore : twoCoreIn (EAt ctx.Γ penultimate) ≤ QAt ctx.Γ penultimate := by
    change twoCoreIn (ctx.Γ.twoResidualAt penultimate) ≤ ctx.Γ.twoCoreAt penultimate
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def,
      SevenSix.residual_core_eq_inter_core]
    exact inf_le_right
  exact ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core penultimate
    ctx.criticalPath.a' ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
    default).2.2 (hcore data.conjugator_mem)

public theorem nine_five_terminal_module_centralizer_le_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) ≤
      QAt ctx.Γ ctx.criticalPath.a' := by
  apply nine_three_module_centralizer_core_at_vertex ctx
  obtain ⟨conjugator, _, hend⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  exact ⟨conjugator, hend⟩

end Stellmacher.SectionNine
