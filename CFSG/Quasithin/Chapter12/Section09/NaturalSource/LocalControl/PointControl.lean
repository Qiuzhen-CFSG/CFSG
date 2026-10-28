module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointModels
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointBound
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.ThreeRadical

/-!
# Point-component escape and the source model list

If the original K₁T lay in M = N_G(L), the containing-component theorem
would give K₁ = L₁. Its actual quotient is then PSLₙ₋₁(2), whose outer
group is a two-group. The proved point-quotient centralizer bound and
Sylow decomposition would force G₁ ≤ M, contrary to the original escape.
Thus K₁T belongs to Hz in both source degrees, without using the later
surviving-model list or proving outer-group facts for every discarded row.

Apply the existing F.9.18 comparison and seven-core exclusion to that
same join. They give the actual A₇, PSL₄(2), or PSL₅(2) quotient. In degree
five the original nested-component comparison leaves only PSL₅(2).
LocalControl applies this family with the original flag and component;
its plane-centralizer bound remains a separate source obligation.

Source: Aschbacher--Smith 12.9.5(1--2), printed pp.860--861 of
refs/quasithin.pdf, using the component comparison from 12.9.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

private theorem small_binary_outer_two {X : Type*} [Group X]
    {d : ℕ} (hd₀ : 3 ≤ d) (hd₁ : d ≤ 5) (hm : ClassicalGroup.IsPSL X d 2) :
    IsPGroup 2 (MulAut.Outer X) := by
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := hm
  let := Fintype.ofFinite k
  let f : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let e := (e₀.trans (Atlas.fieldEquivPSL d f)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < d))
  suffices ho : IsPGroup 2 (MulAut.Outer (BinaryLinear.OuterCyclic.LinearGroup d)) from
    ho.of_equiv (MulAut.outerCongr e).symm
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup d))
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨g,hg | hg⟩ := BinaryLinear.InvariantNodeActions.smallDimension_inner_graph hd₀ hd₁ a
  all_goals have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  · refine ⟨1,?_⟩
    change (q a) ^ (2 ^ 1) = 1
    rw [hg,hi,one_pow]
  · refine ⟨1,?_⟩
    change (q a) ^ (2 ^ 1) = 1
    rw [hg,map_mul,hi,mul_one,pow_one,←map_pow,
      BinaryLinear.OuterCyclic.graphLinear_sq,map_one]

/-- The original point-component Sylow join lies in Hz in both degrees. -/
theorem point_join_mem_Hz_of_abelian
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G)) := by
  have hi : Components.ComponentIndex n 1 := by
    rcases hn with rfl | rfl
    · exact Or.inr ⟨rfl,Or.inl rfl⟩
    · exact Or.inl ⟨rfl,by decide,by decide⟩
  have hc := point_quotient_centralizer_le_normalizer h hn earlier F hab C
  have hout : ¬ C.K1 ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) := by
    intro hXM
    have he := Components.component_eq_of_le_normalizer h earlier F 1 hi
      ⟨C.point_le,C.component⟩ C.contains (le_sup_left.trans hXM)
    have hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) (n-1) 2 := by
      rw [he]
      simpa only [max_eq_right (show 1 ≤ n-1 by rcases hn with rfl | rfl <;> decide)] using
        Components.Li_core_model h F 1 hi
    have ho := small_binary_outer_two (by rcases hn with rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl <;> decide) hm
    exact (point_join_mem_Hz_of_quotient_centralizer h earlier F C ho hc).2.2 hXM
  let X := C.K1 ⊔ (T : Subgroup G)
  have hXH : X ≤ F.H := sup_le C.point_le (F.invariant 1)
  have hZ : F.Vi 1 ≤ X := ((F.le_seed 1).trans h.chosen.le_sylow).trans le_sup_right
  have hcard : Nat.card (F.Vi 1) = 2 := by
    simpa using F.card 1 (by rcases hn with rfl | rfl <;> decide)
  have hcore : X.pCoreIn 2 ≠ ⊥ := by
    have hp : IsPGroup 2 (F.Vi 1) := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have hle := le_pCoreIn_of_normalizes hp hZ hXH
    intro he
    have hz := le_bot_iff.mp (he ▸ hle)
    rw [hz,card_bot] at hcard
    contradiction
  refine ⟨⟨hcore,?_⟩,hXH,hout⟩
  intro g hg
  rcases hg with hg | hg
  · exact mem_sup_left (C.contains hg)
  · exact mem_sup_right hg

/-- Source 12.9.5(2), for the same original flag and containing component. -/
theorem point_models_of_abelian
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 :=
  point_models_of_abelian_join h hn earlier F hab C
    (point_join_mem_Hz_of_abelian h hn earlier F hab C)

/-- In degree five the actual point quotient is PSL₅(2). -/
theorem five_point_model_of_abelian
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 :=
  five_point_model_of_controlled_quotient h earlier F C
    (point_quotient_centralizer_le_normalizer h (Or.inr rfl) earlier F hab C)
    (point_models_of_abelian h (Or.inr rfl) earlier F hab C)
end CFSG.Quasithin.Chapter12.Section09.NaturalSource
