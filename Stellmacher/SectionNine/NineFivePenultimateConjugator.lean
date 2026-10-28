module

public import Stellmacher.SectionNine.NineFivePenultimateCoreNontrivialReduction

/-!
# The penultimate conjugator in Stellmacher (9.5)

The original transvection hypotheses, together with initial center order
four, give a conjugator in the penultimate residual two-core such that the
commutator, its conjugate, and the terminal center generate a group
containing the penultimate center. This is the input used to span the
terminal module with two conjugate four-element quotient supports.

Write R for the actual transvection commutator. If R is contained in the
penultimate center, the two index-two cardinal identities show that R and
the terminal center already generate that center, so the identity is a
suitable conjugator. Otherwise the coprime core-centrality reduction forces
a nontrivial core commutator. The residual-join bound and the line-escape
lemma then give a commutator outside the terminal center, whose conjugating
element provides the required span.

Source: Stellmacher, N-group paper (1997), proof of (9.5), printed pp.52–53,
`refs/files/stellmacher-n-group.pdf`. The printed intermediate blanket
noncentrality assertion is unnecessary: separating the first case above
proves the required conjugator without adding a noncentrality hypothesis.
-/

open scoped commutatorElement

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

/-- The original transvection data give a penultimate residual-core conjugator. -/
public theorem nine_five_penultimate_conjugator_of_initial_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ prev) :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
    ∃ conjugator : G, conjugator ∈ twoCoreIn (EAt ctx.Γ penultimate) ∧
      ZAt ctx.Γ penultimate ≤ (ZAt ctx.Γ ctx.criticalPath.a' ⊔ residual) ⊔
        residual.map (MulAut.conj conjugator⁻¹).toMonoidHom := by
  classical
  let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
  let line := ZAt ctx.Γ ctx.criticalPath.a'
  let plane := ZAt ctx.Γ penultimate
  obtain ⟨hline, hplaneIndex⟩ :=
    nine_five_penultimate_center_layer_of_initial_four ctx.toLocalContext hfour
  by_cases hsmall : residual ≤ plane
  · have hspan : residual ⊔ line = plane := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le hsmall hline)
      change Nat.card plane ≤ Nat.card (residual ⊔ line : Subgroup G)
      change Nat.card plane = 2 * Nat.card line at hplaneIndex
      change Nat.card (residual ⊔ line : Subgroup G) = 2 * Nat.card line at hindex
      omega
    refine ⟨1, (twoCoreIn (EAt ctx.Γ penultimate)).one_mem, ?_⟩
    change plane ≤ (line ⊔ residual) ⊔ _
    exact hspan.symm.le.trans ((sup_comm residual line).le.trans le_sup_left)
  · have hjoin := nine_five_penultimate_residual_le_join_of_initial_four
      ctx hfour hb prev hpath
    have hnontrivial : ⁅twoCoreIn (EAt ctx.Γ penultimate), residual⁆ ≠ ⊥ := by
      intro hcentral
      exact hsmall (nine_five_penultimate_core_centralizes_imp_le_center
        ctx hfour hb prev hpath actor hactor hindex hcontain hcentral)
    have hbound := nine_five_penultimate_core_bound_of_initial_four_and_residual_join
      ctx hfour hb prev hpath actor hactor hindex hcontain hjoin
    have hescape := nine_five_penultimate_core_escape_of_initial_four_and_nontrivial
      ctx hfour hb prev hpath actor hactor hindex hcontain hjoin hnontrivial
    exact nine_five_penultimate_conjugator_of_core_action ctx actor hfour hbound hescape

end Stellmacher.SectionNine
