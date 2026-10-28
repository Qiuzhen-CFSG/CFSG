module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction
public import Theory.GroupTheory.CComponent.ThreeResidual

/-!
# The invariant component is the three-prime residual

The actual binary component quotient has rank two, trivial center and outer
group of order prime to three. An element of order three in its centralizer
would extend an elementary nine to an elementary twenty-seven. Thus the
centralizer has order prime to three. The actual outer conjugation homomorphism
then makes the component index prime to three. Lifting through O₂(H) preserves
that property, giving O^{3′}(H) ≤ L.

This proves the required ordinary A.3.18 outcome directly for the binary models.
No A.3.18 exception, central cover or split/nonsplit extension is assumed away:
the proved center and outer-order facts rule out any extra three-part in H/L.
Together with normal generation and the reverse inclusion from the source X,
this yields the residual equality used on printed p.1164.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.18,
printed pp.51–52, and the second paragraph of 15.4.20, p.1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u


private theorem center_bot_of_equiv {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (hz : center Q = ⊥) : center R = ⊥ := by
  apply eq_bot_iff.mpr
  intro r hr
  have hq : e.symm r ∈ center Q := ((centerCongr e).symm ⟨r, hr⟩).property
  have he : e.symm r = 1 := by simpa only [hz, mem_bot] using hq
  apply mem_bot.mpr
  apply e.symm.injective
  simpa using he


variable {G : Type u} [Group G] [Finite G]
open Chapter1 Chapter1.XiEmbedding.InvariantThree

/-- The invariant binary component contains O^{3′}(H). The proof uses the
actual quotient rank and outer group, rather than assuming a residual identity
or conflating the covers and extensions in A.3.18. -/
theorem binary_residual_le {κ : GroupClass.{u}} {U X P H L : Subgroup G}
    (hH : IsSQTK κ H) (h : XiEmbedding.LocalInput 3 U X P H)
    (hL : L ∈ cComponentsIn H) (hn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 4 2 ∨
      ClassicalGroup.IsPSL (XiQuotient L) 5 2) :
    (primeToResidual 3 H).map H.subtype ≤ L := by
  let N := L.subgroupOf H
  let _ : N.Normal := hn
  let e : (N ⧸ pCore 2 N) ≃* XiQuotient L :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL.1) (pCore_map_iso 2 _)
  have hz : center (XiQuotient L) = ⊥ := by
    rcases hm with hm | hm
    · exact binary_linear_center_eq_bot (by decide : 0 < 4) hm
    · exact binary_linear_center_eq_bot (by decide : 0 < 5) hm
  have hr : 2 ≤ primeRank 3 (N ⧸ pCore 2 N) := by
    rw [primeRank_equiv 3 e]
    exact (component_quotient_rank h hH.stronglyQuasithin hL.1
      ((le_sup_right.trans h.complement.le).trans hXL)).2.ge
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (N ⧸ pCore 2 N))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact BinaryAction.binary_outer_prime_to_three_of_models hm
  have hi := cComponent_index_coprime_three_of_quotient N hL.2 (center_bot_of_equiv e.symm hz)
    hr (hH.stronglyQuasithin 3 (by decide) (by decide)) ho
  exact (map_mono (f := H.subtype) (primeToResidual_le N hi)).trans_eq
    (map_subgroupOf_eq_of_le hL.1)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
