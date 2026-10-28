module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification

/-!
# Numerical exclusion for the actual natural-dual MS input

For the supplied nonzero point x, the earlier theta, inner-action and
projected-action formulas construct the literal BinaryMS input on
J = O²(P)S, D = O²(P), and the original S. The marked construction retains
J = PS and the Sylow embedding. ResidualStructure proves |[O₂(J),D]| ≥ 128
and |Z([O₂(J),D])| ≥ 16 for this same input.

The source core and binary commutator core coincide by definition. The
source's mapped center has the same cardinality as the intrinsic center
through the injective subgroup inclusion. Thus cases (1), (2), and (5) of
the full C.1.34 witness contradict the core bound, and case (3) contradicts
the center bound. Case (4) contradicts 15.3.8 through the original Sylow
marking and the unchanged index and center-order hypotheses.

`false_of_inner` constructs the input and applies that full classification.
It retains the explicit same-point projected-action premise and the exact
earlier-source implications for the 15.3.24 assembly owner. It does not
assert the unresolved equality in MSData or unconditional completion of
15.3.24. Both choices of Hypothesis 15.3.10 remain available.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(12), 15.3.17(2), 15.3.24, printed pp.1123–1130, and C.1.31–34,
printed pp.135–137.
-/

public section
open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.NumericClassification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {d : LocalData G} {L I : Subgroup G}

/-- Both source conventions define the same subgroup [O₂(D),K]. -/
theorem sourceQ_eq_commutatorCore {D : Type*} [Group D] (K : Subgroup D) :
    sourceQ K = ChapterC.BinaryMS.commutatorCore K := rfl

/-- The source's mapped center has the order of the intrinsic binary core center. -/
theorem sourceCenter_card {D : Type*} [Group D] (K : Subgroup D) :
    Nat.card (sourceCenter K) =
      Nat.card (center (ChapterC.BinaryMS.commutatorCore K)) := by
  exact (Nat.card_congr ((center (sourceQ K)).equivMapOfInjective
    (sourceQ K).subtype (sourceQ K).subtype_injective).toEquiv).symm

private theorem natural_upper_card {D : Type*} [Group D] {K A : Subgroup D}
    {e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    {a : ℕ} (n : LayerModel K A ⊥ e (NaturalCopies (ZMod 2) a)) :
    Nat.card A = 8 ^ a := by
  rw [Nat.card_congr n.upperIso.toEquiv]
  simp [Nat.card_eq_fintype_card]

private theorem natural_quotient_card {D : Type*} [Group D] {K A B : Subgroup D}
    {e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    {a : ℕ} (n : LayerModel K A B e (NaturalCopies (ZMod 2) a)) :
    Nat.card A = 8 ^ a * Nat.card B := by
  let := n.lower_normal
  rw [card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A),
    Nat.card_congr n.quotientIso.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe n.lower_le).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The literal residual input, original Sylow marking, PS identity, and
intrinsic bounds are constructed on the same supplied point. -/
theorem exists_marked_binaryInput_of_inner [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) (plane : PlaneParabolic d L h.model)
    {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (hi : Preparation.IsInnerOnComponent d L
      ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)))
    (hSP : d.S ⊓ L ≤ point h x)
    (hf : HasCharacteristicTwo I) (hq : IsSQTK κ I)
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L)
    (hact : ⁅projectedCenter d L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)⁆ ≠ ⊥)
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal) :
    ∃ _input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x),
      Chapter1.IsSylowIn 2 d.S (residualOvergroup h x) ∧
      residualOvergroup h x = point h x ⊔ d.S ∧
      128 ≤ Nat.card (ChapterC.BinaryMS.commutatorCore (residualComponent h x)) ∧
      16 ≤ Nat.card (center (ChapterC.BinaryMS.commutatorCore (residualComponent h x))) := by
  obtain ⟨input⟩ := exists_binaryInput_of_inner h plane hx hS hθ hi hSP hf hq hsplit hact h11
  exact ⟨input, residualOvergroup_sylow h x (hθ ▸ theta_le I) hS,
    residualOvergroup_eq_join h x (sylow_intersection_of_eq_theta d hS hθ) hSP,
    binaryInput_core_bounds_of_theta h hx hS hθ input⟩

/-- Every C.1.34 alternative contradicts the actual intrinsic residual geometry.
The bounds are proved here from theta, not assumed from MSData. -/
theorem not_source_alternatives [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (S : Sylow 2 (residualOvergroup h x))
    (hmark : (S : Subgroup (residualOvergroup h x)).map (residualOvergroup h x).subtype = d.S)
    (e : (residualComponent h x ⧸ pCore 2 (residualComponent h x)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (ha : Alternatives (ZMod 2) 1 (residualComponent h x) (sylowPart h x) S e) :
    False := by
  obtain ⟨hQ, hC⟩ := binaryInput_core_bounds_of_theta h hx hS hθ input
  rw [← sourceQ_eq_commutatorCore] at hQ
  rw [← sourceCenter_card] at hC
  let := input.component_normal
  have hr := LinearThree.local_centralOmega_rank_le_two d (residualOvergroup h x)
    S hmark hindex hZ hZS
  rcases LinearThree.alternatives_without_four S hr ha with ha | ha
  · cases ha with
    | one _ hn =>
      obtain ⟨n⟩ := hn
      have hc := natural_upper_card n
      norm_num at hc
      omega
    | two hn _ =>
      obtain ⟨n⟩ := hn
      have hc := natural_upper_card n
      norm_num at hc
      omega
    | three hn _ _ =>
      obtain ⟨n⟩ := hn
      have hc := natural_upper_card n
      norm_num at hc
      omega
  · obtain ⟨n⟩ := ha.natural
    have hc := natural_quotient_card n
    rw [ha.fixed_order] at hc
    norm_num at hc
    omega

/-- Apply the full universal C.1.34 witness to the actual residual input;
the original Sylow marking is reconstructed from the source Sylow hypothesis. -/
theorem false_of_binaryInput [IsElementaryAbelian 2 (d.componentSpan L)]
    (classification : UniversalClassification.{u})
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) : False := by
  obtain ⟨S, hmark⟩ := residualOvergroup_sylow h x (hθ ▸ theta_le I) hS
  have hRS : sylowPart h x ≤ (S : Subgroup (residualOvergroup h x)) := by
    intro s hs
    have hm : (s : G) ∈ (S : Subgroup (residualOvergroup h x)).map
        (residualOvergroup h x).subtype := hmark.symm ▸ hs
    obtain ⟨t, ht, he⟩ := hm
    exact (Subtype.ext he : t = s) ▸ ht
  obtain ⟨e, he⟩ := classification κ (residualOvergroup h x)
    (residualComponent h x) (sylowPart h x) (binaryInput_sourcePair input)
    (ZMod 2) 1 (by decide) (by simp) ⟨input.quotientEquiv⟩ S hRS
  exact not_source_alternatives h hx hS hθ input hindex hZ hZS S hmark e he

/-- The numerical exclusion for the literal input constructed at x. The
projected-action producer and earlier source theorems remain explicit inputs
for the 15.3.24 assembly owner, which must supply them for this same x. -/
theorem false_of_inner [IsElementaryAbelian 2 (d.componentSpan L)]
    (classification : UniversalClassification.{u})
    (h : NaturalDual d L) (plane : PlaneParabolic d L h.model)
    {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (hi : Preparation.IsInnerOnComponent d L
      ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)))
    (hSP : d.S ⊓ L ≤ point h x)
    (hf : HasCharacteristicTwo I) (hq : IsSQTK κ I)
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L)
    (hact : ⁅projectedCenter d L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)⁆ ≠ ⊥)
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) : False := by
  obtain ⟨input, _, _, _, _⟩ :=
    exists_marked_binaryInput_of_inner h plane hx hS hθ hi hSP hf hq hsplit hact h11
  exact false_of_binaryInput classification h hx hS hθ input hindex hZ hZS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.NumericClassification
