module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition.SwapExtension
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition.ModelComparison
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models

/-!
# Natural-action recognition on the component join in G.9.3

The two surviving factor dimensions give actual action identifications on
H = L join L₂. Dimension two yields the nonprojective Ω₄⁺(2ⁿ) model with
n > 1. Dimension three yields the PSL₃(2) tensor model, n = 1 and m₂(L) = 2.
The original actor A and its rank m are retained, including possible swaps.

The earlier section-rank and A.1.34 inputs, and the numerical part of the
low-dimensional rank-one classification, remain explicit source obligations.
No natural factor representation is assumed: faithful matrix images, their
orders and perfectness construct both group isomorphisms and intertwiners.
The parent must discharge these earlier inputs before asserting the source
classification; the definition SmallModuleOrderTheorem supplies no witness.

The printed whole-G assertion in (14) is stronger than the argument on
p.356. The complete SwapExtension diagnostics and all old public interfaces
are preserved. The adequate three-dimensional result here concerns H.

Source: Aschbacher--Smith, combined manuscript, G.9.3(14),(15), printed
pp.354,356 (PDF pp.365,367).
-/

@[expose] public noncomputable section

open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition

open Theory.GroupTheory Subgroup
open FactorReduction.ModelRestrictions

universe u v

/-- The numerical part of the low-dimensional rank-one classification used
on printed p.356. This is an explicit earlier classification obligation, not
an inhabited record and not an assumption about either tensor action.
`QuotientModel` is the full concrete A.1.34 list, including Suzuki, J₁ and
odd-field PSL₂; the Schur hypothesis concerns the full binary commutant. -/
def SmallModuleOrderTheorem : Prop :=
  ∀ (S : Type u) [Group S] [Finite S], QuotientModel S →
    ∀ (F : Type v) [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
      (I : Type v) [AddCommGroup I] [Module F I] [Module (ZMod 2) I]
      [IsScalarTower (ZMod 2) F I] [FiniteDimensional F I]
      (σ : Representation F S I),
      Representation.IsIrreducible (Representation.restrictScalars (k := ZMod 2) σ) →
      Function.Injective σ →
      (∀ f : Representation.IntertwiningMap
        (Representation.restrictScalars (k := ZMod 2) σ)
        (Representation.restrictScalars (k := ZMod 2) σ), ∃ c : F, ∀ x, f x = c • x) →
      (Module.finrank F I = 2 → Nat.card S = Nat.card SL(2, GaloisField 2 (Module.finrank (ZMod 2) F))) ∧
      (Module.finrank F I = 3 → Module.finrank (ZMod 2) F = 1 ∧ Nat.card S = 168)

variable {G : Type u} [Group G] [Finite G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L L₂ H : Subgroup G} {m : ℕ}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The binary field is impossible: the actual faithful special-linear image
would make the nontrivial perfect component a subgroup of solvable PSL₂(2). -/
theorem two_dimensional_field_degree (T : TensorData ρ L L₂)
    (hL : IsComponent G L) (hk : T.k = 2)
    (ho : Nat.card L = Nat.card SL(2,GaloisField 2 T.n)) : 1 < T.n := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ Subgroup.center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  obtain ⟨e, _, _⟩ := natural_coordinates_of_order T.left T.left_faithful hk
    T.fieldEquiv.toRingEquiv ho
  by_contra hn
  have hn1 : T.n = 1 := by have := T.n_pos; omega
  let : Group.IsSolvable (Theory.PSL2.Group (GaloisField 2 T.n)) :=
    Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by
      rw [GaloisField.card 2 T.n T.n_pos.ne', hn1]; norm_num)
  let ep := e.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 T.n))
  exact Group.IsPerfect.not_isSolvable L
    (Group.isSolvable_of_isSolvable_injective (f := ep.toMonoidHom) ep.injective)


private theorem component_small_orders (hA : SemisimpleSectionRankTheorem K)
    (hs : SourceA134Three K) (hsmall : SmallModuleOrderTheorem.{u,v})
    (h : ComponentHypothesis K ρ A L H m)
    (h₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (e : L ≃* L₂) (T : TensorData ρ L L₂) :
    (T.k = 2 → Nat.card L = Nat.card SL(2, GaloisField 2 T.n)) ∧
    (T.k = 3 → T.n = 1 ∧ Nat.card L = 168) := by
  have hz := component_center_eq_bot hA h h₂ hne e T
  have hm := source_quotient_models hA hs h h₂ hH hne e
  let ez : L ≃* (L ⧸ center L) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact hsmall L (hm.of_equiv ez) T.F T.I T.left
    T.left_irreducible T.left_faithful T.left_schur

/-- The two-dimensional branch of G.9.3 on the supplied component join.
Only the earlier section-rank, A.1.34 and numerical small-module theorems
remain explicit. All group, field and action comparisons are constructed. -/
theorem dimension_two_recognition (hA : SemisimpleSectionRankTheorem K)
    (hs : SourceA134Three K) (hsmall : SmallModuleOrderTheorem.{u,v})
    (h : ComponentHypothesis K ρ A L H m)
    (h₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (e : L ≃* L₂) (T : TensorData ρ L L₂) (hk : T.k = 2) :
    1 < T.n ∧ Quasiequivalent (ρ.comp H.subtype) (fourOrthogonal T.n) := by
  have ho := (component_small_orders hA hs hsmall h h₂ hH hne e T).1 hk
  let : IsQuasisimple L := h.component.2
  let : IsQuasisimple L₂ := h₂.2
  have hz := component_center_eq_bot hA h h₂ hne e T
  have hd := component_pair_disjoint_of_center_eq_bot h.component h₂ hne hz
  refine ⟨two_dimensional_field_degree T h.component hk ho, quasiequivalent_trans
    (tensor_natural_of_order T (h.component.commutator_eq_bot_of_ne h₂ hne) hd hH
      T.fieldEquiv hk ho ((Nat.card_congr e.toEquiv).symm.trans ho))
    (naturalTensor_fourOrthogonal T.n)⟩

/-- The adequate three-dimensional branch identifies the action of the
actual normal component join H. The original A and m are retained. -/
theorem dimension_three_recognition (hA : SemisimpleSectionRankTheorem K)
    (hs : SourceA134Three K) (hsmall : SmallModuleOrderTheorem.{u,v})
    (h : ComponentHypothesis K ρ A L H m)
    (h₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (e : L ≃* L₂) (T : TensorData ρ L L₂) (hk : T.k = 3) :
    T.n = 1 ∧ primeRank 2 L = 2 ∧
      Quasiequivalent (ρ.comp H.subtype) threeTensor := by
  obtain ⟨hn, ho⟩ := (component_small_orders hA hs hsmall h h₂ hH hne e T).2 hk
  let : IsQuasisimple L := h.component.2
  let : IsQuasisimple L₂ := h₂.2
  let c : T.F ≃ₐ[ZMod 2] ZMod 2 :=
    (Module.nonempty_algEquiv_iff_finrank_eq_one.mpr hn).some.symm
  have horder : Nat.card L = Nat.card SL(3,ZMod 2) := ho.trans Matrix.PSL3Two.card_SL.symm
  obtain ⟨a, _, _⟩ := natural_coordinates_of_order T.left T.left_faithful hk c.toRingEquiv horder
  have hr : primeRank 2 L = 2 := by
    rw [primeRank_equiv 2
      (a.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)).symm)]
    exact Matrix.PSL3Even.two_rank (ZMod 2) (n := 1) (by decide) (by simp)
  have hz := component_center_eq_bot hA h h₂ hne e T
  have hd := component_pair_disjoint_of_center_eq_bot h.component h₂ hne hz
  exact ⟨hn, hr, quasiequivalent_trans
    (tensor_natural_of_order T (h.component.commutator_eq_bot_of_ne h₂ hne) hd hH c hk
      horder ((Nat.card_congr e.toEquiv).symm.trans horder)) naturalTensor_threeTensor⟩

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition
