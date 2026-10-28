module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentMathieuExclusion
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The original rank-two image in the intrinsic centralizer core

Restrict the original KL₁V action to a Sylow E₉ of L₁ and then to the
centralizer of the marked V-hat inside X-hat. Condition (*) places its
literal quotient image in O₃(C/O₂(C)). Faithfulness on the selected simple
component and coprimality with O₂(C) make this map injective. Thus this
specific three-core has three-rank at least two, as required in the
remaining Theorem C inspection.

The earlier TI and nonsingular-centralizer inputs remain explicit. This
is not yet the simple-row exclusion or the abelian point-span conclusion.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, last paragraph.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn in
/-- The original Sylow embeds in the precise three-core, compatibly with both quotient maps. -/
theorem SourceHypothesis.original_rank_two_core_embedding
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    ∃ f : P →* C, ∃ g : P →* pCore 3 (C ⧸ pCore 2 C),
      (∀ x, (f x).val.val = a.residualSylowAction P x) ∧
      (∀ x, (g x).val = QuotientGroup.mk' (pCore 2 C) (f x)) ∧
      Function.Injective g := by
  let E := D.fullSetup hZ T z
  let A₀ := (E.L₁.subgroupOf c.localActor).map a.action
  let A := A₀.subgroupOf a.action.range
  let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
  let C := centralizer (U : Set a.action.range)
  let j : P →* c.localActor :=
    (inclusion (show E.L₁ ≤ c.localActor from le_sup_right.trans le_sup_left)).comp
      (P : Subgroup E.L₁).subtype
  let r : P →* a.action.range := a.action.rangeRestrict.comp j
  have hA (x : P) : r x ∈ A :=
    ⟨j x,x.val.property,rfl⟩
  let f : P →* C := r.codRestrict C (by
    intro x u hu
    exact Subtype.ext (a.residual_centralizes (hA x) u.val hu))
  have hf : Function.Injective f := by
    intro x y he
    apply S.original_rank_two_sylow_faithful D hZ z hz hTV hTz hbound hH hn c a hTI hns hr P
    exact congrArg (fun b : C => b.val.val) he
  let q := QuotientGroup.mk' (pCore 2 C)
  let g : P →* pCore 3 (C ⧸ pCore 2 C) := (q.comp f).codRestrict _ (by
    intro x
    exact S.original_action_residual_le_centralizer_twoThreeCore D hZ z hz hTV hTz hbound hH hn c a (hA x))
  refine ⟨f,g,fun _ => rfl,fun _ => rfl,?_⟩
  have hdis : Disjoint f.range (pCore 2 C) :=
    (P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).disjoint_of_coprime
      pCore_isPGroup (by decide)
  apply (MonoidHom.ker_eq_bot_iff g).mp
  apply bot_unique
  intro x hx
  have hqx : q (f x) = 1 := congrArg Subtype.val hx
  have hfx : f x = 1 := hdis.le_bot
    ⟨⟨x,rfl⟩,(QuotientGroup.eq_one_iff _).mp hqx⟩
  exact hf (hfx.trans f.map_one.symm)

include hz hTV hTz hbound hH hn in
/-- Condition (*) forces rank at least two in the actual centralizer quotient core. -/
theorem SourceHypothesis.original_rank_two_centralizer_core_rank
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) := by
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  obtain ⟨_,g,_,_,hg⟩ := S.original_rank_two_core_embedding D hZ z hz hTV hTz hbound hH hn c a hTI hns hr P
  obtain ⟨hP,hcard⟩ := S.original_point_residual_sylow D hZ z hz hTz P
  let := hP
  let : IsElementaryAbelian 3 g.range :=
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  apply IsElementaryAbelian.primeRank_ge_of_card g.range
  exact (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm.trans hcard
end CFSG.Quasithin.Chapter12.Section06
