module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.HigherLinear
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.FiveComponentCentralizer
public import Theory.GroupAction.AutomorphismFixerInnerGraph

/-!
# The PSL₅(2)–A₆ pair fixer

The actual natural-model equivalence sends the embedded component to a
centerless subgroup of order 360 in GL₅(2). Its centralizer is trivial:
a five-subgroup bounds the centralizer order by a divisor of fifteen,
whereas the direct-product order calculation makes it divide 27776.
Consequently the pointwise automorphism fixer embeds into the outer
quotient. The proved inner/inverse-transpose coverage bounds this quotient,
and hence the full fixer, by two.

The argument applies to every actual A₆ embedding. It does not require an
embedding classification, an involution graph label, or the erroneous
printed elementary-kernel expression in the PSL₅(2) j₂ row.

Source: Aschbacher–Smith, 16.1.4(8), 16.1.7(3e), and the sieve in 16.3.5,
combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] {E L I : Subgroup G} {t i : G}

private theorem center_eq_bot_of_alt6 {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 6)) : center H = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  have he : e x ∈ center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [← map_mul] using congrArg e (mem_center_iff.mp hx z)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  simpa only [map_one] using he

/-- The full pointwise fixer of the actual A₆ component in a PSL₅(2)
enlargement has order at most two. -/
theorem pairFixer_card_le_two_psl5 (h : PairContext E L I t i)
    (hlarge : ClassicalGroup.IsPSL I 5 2)
    (hsmall : Nonempty (L ≃* alternatingGroup (Fin 6))) :
    Nat.card (pairFixer L I) ≤ 2 := by
  obtain ⟨es⟩ := hsmall
  let e := LiePreliminaries.higherLinearEquiv (by decide : 0 < 5) hlarge
  let P := L.subgroupOf I
  let Q := P.map e.toMonoidHom
  let d : P ≃* alternatingGroup (Fin 6) := (subgroupOfEquivOfLe h.proper.le).trans es
  let f : Q ≃* alternatingGroup (Fin 6) :=
    (P.equivMapOfInjective e.toMonoidHom e.injective).symm.trans d
  have hQcard : Nat.card Q = 360 := by
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hQc := BinaryLinear.FiveComponentCentralizer.centralizer_eq_bot Q hQcard
    (center_eq_bot_of_alt6 f)
  have hPc : centralizer (P : Set I) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : e x ∈ centralizer (Q : Set (LinearGroup 5)) := by
      apply mem_centralizer_iff.mpr
      rintro _ ⟨y, hy, rfl⟩
      change e y * e x = e x * e y
      simpa only [map_mul] using congrArg e (mem_centralizer_iff.mp hx y hy)
    rw [hQc, mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))
  apply MulAut.fixing_card_le_two_of_inner_graph P hPc
    ((MulAut.congr e).symm (graphLinear 5))
  intro a
  obtain ⟨g, hg⟩ := inner_graph (Or.inr rfl) (MulAut.congr e a)
  refine ⟨e.symm g, ?_⟩
  rcases hg with hg | hg
  · left
    apply (MulAut.congr e).injective
    simpa only [MulAut.congr_conj, e.apply_symm_apply] using hg
  · right
    apply (MulAut.congr e).injective
    simpa only [map_mul, MulAut.congr_conj, e.apply_symm_apply,
      MulEquiv.apply_symm_apply] using hg

/-- The PSL₅(2) branch of the strict bound in LieBounds.graph_binary. -/
theorem pairFixer_card_lt_four_psl5 (h : PairContext E L I t i)
    (hlarge : ClassicalGroup.IsPSL I 5 2)
    (hsmall : Nonempty (L ≃* alternatingGroup (Fin 6))) :
    Nat.card (pairFixer L I) < 4 :=
  (pairFixer_card_le_two_psl5 h hlarge hsmall).trans_lt (by decide)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
