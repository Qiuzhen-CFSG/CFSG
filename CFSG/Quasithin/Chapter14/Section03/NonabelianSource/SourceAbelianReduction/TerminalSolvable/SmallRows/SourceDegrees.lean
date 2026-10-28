module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5RankOneEntry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.ExchangedA5
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesFullFour
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorFour
public import CFSG.Quasithin.ChapterG.Section10.CoefficientField
public import Theory.Representation.SymplecticFixedLine

/-!
# Original degree inputs for the terminal A₅ branches

The completed 14.3.14 alternatives discharge the same-component radical
comparison and hence identify K/O₂(K) in the normalized A₅ branch. Its
minimal outside parabolic and genuine F.1.1 pair now require no numerical
callback. The field-four recognition and Borel contradiction remain open.

For the actual exchanged tensor, the dimension is eight, so neither larger
actor alternative can occur. The resulting small-actor bound makes the
marked transvection space at least three-dimensional. The coefficient-field
constraint of G.10 then forces the actor outside the literal dotted tensor
span. The intrinsic span quotient and symplectic normalizer contradiction
are applied on that same K, T-span, action and invariant form.

The final larger-actor consumer also discharges the completed degree-four
recognition. The full wreath quotient, normalized field-four recognition,
and final terminal solvability remain with this source family. The actual
tensor ActionModel and A₆ source exclusion retain their independent owners.
Source: Aschbacher–Smith G.10.1, G.11.2(7), 14.3.6 and 14.3.14–15,
printed pp.357,364,991–994.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hyp hK

/-- The original degree theorem supplies every numerical premise of the
same-component radical comparison. -/
theorem source_terminal_small_image_radical (hsmall : SmallImageRow F K) :
    solvableRadical K = pCore 2 K := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  apply hK.radical_eq_twoCore_of_terminal_degrees h hne hgP hgH hyp hsmall
  by_cases hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  · exact Or.inl hm
  · let s : LargeActorSource T M Mc F g B v :=
      ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,
        hK.terminal_not_solvable,hyp,hm⟩
    rcases s.degree_cases with ⟨hd,_⟩ | ⟨hd,hm,_⟩
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr ⟨hd,hm⟩)

/-- The literal normalized A₅ quotient and minimal parabolic have no
remaining numerical or radical premise. -/
theorem source_terminal_single_a5_parabolic
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G)) :
    let H := K ⊔ (T : Subgroup G)
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      (pResidual 2 H).map H.subtype = K ∧ (K.subgroupOf H).Normal ∧
      ChapterB.IsMinimalParabolicOver T H ∧ generalizedFitting H = pCore 2 H ∧
      (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M := by
  exact source_terminal_single_a5_parabolic_of_radical hG T hempty hM hu hmany hcard e
    hnot hK hspan e5 (source_terminal_small_image_radical hG T hempty hM hu hmany hcard e
      hnot F hne g hgP hgH hyp hK (Or.inl ⟨e5⟩))

/-- The actual F.1.1 pair, both Borel identities and opposite S₃ quotient
are available under the original terminal prefix. Field-four recognition
and the resulting 14.3.6(1) contradiction remain to be proved. -/
theorem source_terminal_single_a5_rankOne_amalgam
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G)) :
    let Y := sourceResidual M Mc
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    ChapterF.Source.HypothesisF11 ![K,Y ⊔ S₂] (T : Subgroup G) ∧
      Y = ⁅Y,S₂⁆ ∧ ChapterF.Source.borel K (T : Subgroup G) = M ⊓ K ∧
      ChapterF.Source.borel (Y ⊔ S₂) (T : Subgroup G) = S₂ ∧
      Nonempty (((Y ⊔ S₂ : Subgroup G) ⧸ pCore 2 (Y ⊔ S₂ : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨⟨eK⟩,_⟩ := source_terminal_single_a5_parabolic hG T hempty hM hu hmany hcard e
    hnot F hne g hgP hgH hyp hK e5 hspan
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    rw [hspan]
    exact le_normalizer_conjugateSpanBy K (T : Subgroup G)
  exact source_single_a5_rankOne_amalgam hG T hempty hM hu hmany hcard e hnot K
    hK.local_component hn eK (hK.not_le hM.1.2 e)

/-- Dimension eight excludes the original larger-actor alternatives. This
uses the actual tensor coordinates and does not require the outside marking. -/
theorem source_exchanged_a5_small_actor (m : ExchangedA5.ActionModel F K) :
    finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1 := by
  by_contra hm
  let s : LargeActorSource T M Mc F g B v :=
    ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,
      hK.terminal_not_solvable,hyp,hm⟩
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 :=
    m.coordinates.finrank_eq.trans ClassicalOrthogonal.FourPlusMatrix.Binary.finrank_binary
  rcases s.degree_cases with ⟨h4,_⟩ | ⟨h6,_⟩ <;> omega

/-- The original actor is outside the same tensor span. The small-actor
bound forces the marked transvection space to have dimension at least three;
G.10 then forbids an F₄-linear actor. -/
theorem source_exchanged_a5_actor_not_le_span (m : ExchangedA5.ActionModel F K) :
    ¬ F.terminalDot (F.X g) ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G)) := by
  have hsmall := source_exchanged_a5_small_actor hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hyp hK m
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 :=
    m.coordinates.finrank_eq.trans ClassicalOrthogonal.FourPlusMatrix.Binary.finrank_binary
  have hr := (Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf
      (F.terminalDot (F.X g)))) (QuotientGroup.mk'_surjective _)).trans
    (IsElementaryAbelian.rank_le_finrank (p := 2) (F.terminalDot (F.X g)))
  have hW : 3 ≤ finrank (ZMod 2) (hatSpace F (F.E g)) := by
    have hh := hyp.dimension
    omega
  intro hin
  let k := ClassicalOrthogonal.FourPlusMatrix.Binary.F
  let : Module k (Additive F.Uhat) :=
    Representation.SymplecticFixedLine.coordinateModule m.coordinates
  have hsmul (a : k) (w : Additive F.Uhat) :
      m.coordinates (a • w) = a • m.coordinates w := m.coordinates.apply_symm_apply _
  let : IsScalarTower (ZMod 2) k (Additive F.Uhat) :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      apply m.coordinates.injective
      rw [hsmul,m.coordinates.map_smul]
      exact IsScalarTower.algebraMap_smul k a (m.coordinates w))
  have he (x : F.terminalDot (F.X g)) (w : Additive F.Uhat) :
      m.coordinates (F.terminalRepresentation x w) =
        ClassicalOrthogonal.FourPlusMatrix.Binary.action
          (m.componentEquiv (inclusion hin x)) (m.coordinates w) :=
    m.intertwines (inclusion hin x) w
  have hlin (x : F.terminalDot (F.X g)) (a : k) (w : Additive F.Uhat) :
      F.terminalRepresentation x (a • w) = a • F.terminalRepresentation x w := by
    apply m.coordinates.injective
    rw [hsmul,he,hsmul,he]
    exact (ClassicalOrthogonal.FourPlusMatrix.matrixAction
      (m.componentEquiv (inclusion hin x))).map_smul a _
  have hc := hyp.coefficient_card_le_two hlin hW
  have hfour : Nat.card k = 4 := by
    rw [Nat.card_eq_fintype_card]
    exact Representation.SL2FourNatural.card_field
  omega

/-- The same tensor normal span has its exact intrinsic quotient, without
an additional actor, kernel or numerical premise. -/
theorem source_exchanged_a5_span_quotient (m : ExchangedA5.ActionModel F K) :
    Nonempty ((conjugateSpanBy K (T : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G))) ≃* ExchangedA5.ModelGroup) := by
  exact source_exchanged_a5_span_quotient_of_small_actor hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp
    (source_exchanged_a5_small_actor hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hyp hK m) hK m

/-- The original tensor exclusion now requires only the full local wreath
quotient. The actual tensor ActionModel remains independently produced. -/
theorem source_exchanged_a5_false_of_wreath (m : ExchangedA5.ActionModel F K)
    (eJ : ((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Wreath) : False := by
  exact source_exchanged_a5_false_of_small_actor_and_wreath hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp
    (source_exchanged_a5_small_actor hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hyp hK m) hK m
    (ClassicalOrthogonal.FourPlusMatrix.Binary.symplecticNormalizer_card_le (m.form B)
      (m.form_nondegenerate hyp.nondegenerate) (m.form_invariant B hyp.preserves)) eJ
end Source

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The completed numerical and four-dimensional recognition families feed
the original component consumer. Only the independently owned A₆ exclusion remains. -/
theorem component_of_source_four
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    (∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
      ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
    (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
      Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
      F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
        pCore 2 (K.subgroupOf F.H)) :=
  s.component_of_source_degrees
    (fun hd D hD _ => terminal_component_smallImage_of_four F s.hypothesis hd D hD) hsix
end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
