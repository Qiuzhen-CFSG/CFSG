module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# The fixed space and remaining component alternatives in E.6.23

An escaping component of a corank-two centralizer has fixed space exactly
that corank-two subspace. Indeed a larger fixed space has corank one (corank
zero contradicts escape), and restriction would make the same quasisimple
subgroup a component of a hyperplane centralizer of characteristic two.

Consequently the rank-one alternatives of E.6.8 vanish. E.6.18 and the
odd-core argument remove the alternating-seven and triple-cover alternatives.
The remaining Borel alternative has parameter two, and its Suzuki case is
impossible arithmetically. All central two-covers in the linear-three case
are retained. The actual model-centralizer inspections remain separate
obligations; this module does not assert the A₆ conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
E.6.18, E.6.21–23, printed pp.247–248,252–254 (PDF pp.258–259,263–265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open ComponentBalance Components

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

omit [Finite G] in
/-- Restrict a component only to a smaller overgroup which still contains it.
Quasisimplicity is transported between the two nested-subgroup carriers. -/
theorem component_restrict_centralizer {A B X : Subgroup G} (hAB : A ≤ B)
    (hX : CentralizerComponent A X) (hXB : X ≤ centralizer (B : Set G)) :
    CentralizerComponent B X := by
  let e : X.subgroupOf (centralizer (A : Set G)) ≃*
      X.subgroupOf (centralizer (B : Set G)) :=
    (subgroupOfEquivOfLe hX.1).trans (subgroupOfEquivOfLe hXB).symm
  let _ := hX.2.2
  let _ := IsQuasisimple.of_mulEquiv e
  exact ⟨hXB, hX.2.1.comap (inclusion (Subgroup.centralizer_le hAB)), inferInstance⟩

private theorem component_not_characteristicTwo {A X : Subgroup G} (hX : CentralizerComponent A X)
    (hchar : generalizedFitting (centralizer (A : Set G)) =
      pCore 2 (centralizer (A : Set G))) : False := by
  have hl := component_le_generalizedFitting _ _ hX.2
  rw [hchar] at hl
  have hp := (pCore_isPGroup (p := 2) (G := centralizer (A : Set G))).to_le hl
  let _ := hp.isNilpotent
  let _ := hX.2.2
  let _ : IsSimpleGroup ((X.subgroupOf (centralizer (A : Set G))) ⧸
      center (X.subgroupOf (centralizer (A : Set G)))) := IsQuasisimple.simple
  let _ : Nontrivial (X.subgroupOf (centralizer (A : Set G))) :=
    (QuotientGroup.mk'_surjective (center (X.subgroupOf (centralizer (A : Set G))))).nontrivial
  exact Group.IsPerfect.not_isSolvable (X.subgroupOf (centralizer (A : Set G))) inferInstance

private theorem eq_of_corank_eq [IsElementaryAbelian 2 V] {A B : Subgroup G}
    (hAB : A ≤ B) (hBV : B ≤ V)
    (hc : subgroupCorank V A = subgroupCorank V B) : A = B := by
  have hmul := relIndex_mul_relIndex A B V hAB hBV
  have ha : A.relIndex V = 2 ^ subgroupCorank V A := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact relIndex_eq_two_pow_quotient_finrank V A
  have hb : B.relIndex V = 2 ^ subgroupCorank V B := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact relIndex_eq_two_pow_quotient_finrank V B
  rw [ha, hb, hc] at hmul
  have hidx : A.relIndex B = 1 := by nlinarith [Nat.two_pow_pos (subgroupCorank V B)]
  exact le_antisymm hAB (relIndex_eq_one.mp hidx)

/-- The action of an escaping corank-two component has corank exactly two.
The hyperplane input is precisely the earlier E.6.22 conclusion. -/
theorem component_actionCorank_two [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    {A X : Subgroup G} (hAV : A ≤ V) (hc : subgroupCorank V A = 2)
    (hX : CentralizerComponent A X) (he : ¬ X ≤ M) : actionCorank V X = 2 := by
  have hAF : A ≤ V ⊓ centralizer (X : Set G) := fixedSpace_contains hAV hX.1
  have hbound := subgroupCorank_antitone (V := V) hAF
  have hpos := fixedSpace_corank_pos h he
  have hn : subgroupCorank V (V ⊓ centralizer (X : Set G)) ≠ 1 := by
    intro hf
    have hXF : X ≤ centralizer (V ⊓ centralizer (X : Set G) : Set G) :=
      le_centralizer_iff.mpr inf_le_right
    exact component_not_characteristicTwo (component_restrict_centralizer hAF hX hXF)
      (hchar _ ⟨inf_le_left, hf⟩)
  change subgroupCorank V (V ⊓ centralizer (X : Set G)) = 2
  omega

/-- The full fixed space is the originally supplied subspace A, not an
unrelated subspace of the same dimension. -/
theorem component_fixedSpace_eq [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    {A X : Subgroup G} (hAV : A ≤ V) (hc : subgroupCorank V A = 2)
    (hX : CentralizerComponent A X) (he : ¬ X ≤ M) :
    V ⊓ centralizer (X : Set G) = A := by
  apply Eq.symm
  apply eq_of_corank_eq (fixedSpace_contains hAV hX.1) inf_le_left
  exact hc.trans (component_actionCorank_two h hchar hAV hc hX he).symm

/-- E.6.18 and odd-core vanishing remove all three exceptional alternating
models, including both actual triple covers. -/
theorem not_alternatingAlternative (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    {A X : Subgroup G} (hA : A ∈ obstructionFamily M V)
    (hc : subgroupCorank V A = 2) (hX : CentralizerComponent A X) :
    ¬ AlternatingAlternative M V A X := by
  intro b
  rcases b.model with hm | hm | hm
  · exact h18 A hA (by omega) X hX (Or.inl hm)
  · exact centralizerComponent_not_threeCover h21 hA.1 hA.2.1 hX 6 hm
  · exact centralizerComponent_not_threeCover h21 hA.1 hA.2.1 hX 7 hm

/-- The genuine five-way E.6.8 output reduces to its two characteristic-two
branches. No model centralizer or relative normality conclusion is assumed. -/
theorem remaining_alternatives (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    {A Q X : Subgroup G} (hA : A ∈ obstructionFamily M V)
    (hc : subgroupCorank V A = 2) (hX : CentralizerComponent A X)
    (hr : actionCorank V X = 2) (b : ComponentAlternatives M V A Q X) :
    BorelAlternative M V A X 2 ∨ ∃ n, SymplecticAlternative M V A X n := by
  rcases b with ⟨n, b⟩ | b | b | b | b
  · left
    have hn : n = 2 := b.dimension.trans hr
    exact hn ▸ b
  · exact Or.inr b
  · have := b.dimension
    omega
  · exact (not_alternatingAlternative h18 h21 hA hc hX b).elim
  · have := b.dimension
    omega

omit [Finite G] in
/-- Every surviving Borel model is retained with its actual isomorphism or
central two-cover. In particular no centerlessness assumption is introduced. -/
theorem borel_models_at_two {A X : Subgroup G} (b : BorelAlternative M V A X 2) :
    ClassicalGroup.IsPSL X 2 4 ∨ ClassicalGroup.IsPSL X 3 4 ∨
      ClassicalGroup.IsPSU X 3 4 ∨
      (IsPGroup 2 (center X) ∧ ClassicalGroup.IsPSL (X ⧸ center X) 3 4) := by
  rcases b.model with ⟨_, hm⟩ | ⟨m, hm, hn, _⟩ | ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, hz, hm⟩
  · exact Or.inl hm
  · omega
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr (Or.inl hm))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, hm⟩))

/-- Restrict the original block to C_X(U). This establishes subnormality,
not the stronger relative normality still needed in the final configuration. -/
theorem block_in_component_centralizer {U L X : Subgroup G}
    (hL : SmallBlock U L) (hLX : L ≤ X) :
    ChapterC.IsBlock (L.subgroupOf (X ⊓ centralizer (U : Set G))) := by
  have hLC : L ≤ X ⊓ centralizer (U : Set G) := le_inf hLX hL.1
  exact ⟨inferInstance,
    (hL.2.1.short.of_mulEquiv (subgroupOfEquivOfLe hL.1)).of_mulEquiv
      (subgroupOfEquivOfLe hLC).symm,
    hL.2.1.subnormal.comap (inclusion inf_le_right)⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
