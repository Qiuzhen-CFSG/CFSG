module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Layers.UpperPreparation
public import Theory.Representation.BinaryConjugationSection.Generation
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The original upper-layer generation consumer in 11.5.7

The actual S/S₃ and S₃/S₂ are binary modules with the literal quotient
projections. Their conjugation actions are constructed from the source frame;
no homogeneous-module recognition is used in this construction.

Full displacement under the solvable residual on S/S₃, and displacement
supplemented by the opposite pair on S₃/S₂, lift to S=[S,L₁]E.
Trivial Cartan fixed spaces on both quotients put C_S(X) in S₂. Coprime
commutator generation then gives S≤[S,X](S∩U). The final application feeds
these two identities into the original core-containment and collapse theorem.

The residual displacement and Cartan fixed-space calculations remain explicit
mathematical inputs. They must be proved on the genuine natural and dual
modules before this is a proof of the source generation identities. The lower
opposite-pair identity and preceding Chapter 11 inputs keep their independent
source owners. No cohomology or splitting premise is needed for this lifting.

Source: Aschbacher--Smith, 11.5.7, printed pp.781--782; G.2.5, pp.335--336.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open ChapterG.Section02.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
  (hUT : E.W ≤ (T : Subgroup G))
  (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)

/-- The two literal quotient actions. No generation or fixed-space claim is a field. -/
structure UpperActions (E : Geometry D) (x y : G)
    [((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal]
    [((triple E x y).subgroupOf (thirdLayer E x y)).Normal]
    [IsElementaryAbelian 2 ((threeCore E x y ⧸ (thirdLayer E x y).subgroupOf (threeCore E x y)))]
    [IsElementaryAbelian 2 ((thirdLayer E x y ⧸ (triple E x y).subgroupOf (thirdLayer E x y)))] where
  upperAction : Representation (ZMod 2) (threeGroup E x y)
    (Additive ((threeCore E x y ⧸ (thirdLayer E x y).subgroupOf (threeCore E x y))))
  upperSection : BinaryConjugationSection (threeGroup E x y) (threeCore E x y)
    (thirdLayer E x y) upperAction
  upper_coordinates (a : threeCore E x y) : upperSection.coordinates a =
    Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' ((thirdLayer E x y).subgroupOf (threeCore E x y)) a))
  lowerAction : Representation (ZMod 2) (threeGroup E x y)
    (Additive ((thirdLayer E x y ⧸ (triple E x y).subgroupOf (thirdLayer E x y))))
  lowerSection : BinaryConjugationSection (threeGroup E x y) (thirdLayer E x y)
    (triple E x y) lowerAction
  lower_coordinates (a : thirdLayer E x y) : lowerSection.coordinates a =
    Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' ((triple E x y).subgroupOf (thirdLayer E x y)) a))

/-- Construct both actions from the source frame, with no recognition premise. -/
def sourceUpperActions :
    letI : ((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal :=
      d.S₃_normal_in_S hUT hf
    letI : ((triple E x y).subgroupOf (thirdLayer E x y)).Normal :=
      Recognition.Hypothesis.lower_normal d hUT hf (d.L_le_I hUT hf)
    letI : IsElementaryAbelian 2 (threeCore E x y ⧸
      (thirdLayer E x y).subgroupOf (threeCore E x y)) := d.upper_elementary_of_source hUT hf
    letI : IsElementaryAbelian 2 (thirdLayer E x y ⧸
      (triple E x y).subgroupOf (thirdLayer E x y)) :=
      Recognition.Hypothesis.lower_elementary d hUT hf (d.L_le_I hUT hf)
    UpperActions E x y := by
  letI : ((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal :=
      d.S₃_normal_in_S hUT hf
  letI : ((triple E x y).subgroupOf (thirdLayer E x y)).Normal :=
      Recognition.Hypothesis.lower_normal d hUT hf (d.L_le_I hUT hf)
  letI : IsElementaryAbelian 2 (threeCore E x y ⧸
      (thirdLayer E x y).subgroupOf (threeCore E x y)) := d.upper_elementary_of_source hUT hf
  letI : IsElementaryAbelian 2 (thirdLayer E x y ⧸
      (triple E x y).subgroupOf (thirdLayer E x y)) :=
      Recognition.Hypothesis.lower_elementary d hUT hf (d.L_le_I hUT hf)
  apply Classical.choice
  have hn := threeGroup_normalizes_thirdLayer E d hUT hf
  obtain ⟨σ, s, hs⟩ := d.upper_action_of_source hUT hf hn
  obtain ⟨τ, t, ht⟩ := d.lower_action_of_source hUT hf hn
  exact ⟨{
    upperAction := σ.comp (d.sourceStarComparison hUT hf).projection
    upperSection := s
    upper_coordinates := hs
    lowerAction := τ.comp (d.sourceStarComparison hUT hf).projection
    lowerSection := t
    lower_coordinates := ht }⟩

namespace UpperActions
variable {E}
  [((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal]
  [((triple E x y).subgroupOf (thirdLayer E x y)).Normal]
  [IsElementaryAbelian 2 ((threeCore E x y ⧸ (thirdLayer E x y).subgroupOf (threeCore E x y)))]
  [IsElementaryAbelian 2 ((thirdLayer E x y ⧸ (triple E x y).subgroupOf (thirdLayer E x y)))]
  (a : UpperActions E x y)

/-- The quotient calculations lift through S₃ and S₂, preserving the solvable residual. -/
theorem threeCore_eq_of_residual_calculations
    (hupper : Coinvariants.ker (a.upperAction.comp
      (inclusion (pointResidual_le_threeGroup E d hUT hf))) = ⊤)
    (hlower : Coinvariants.ker (a.lowerAction.comp
      (inclusion (pointResidual_le_threeGroup E d hUT hf))) ⊔
        a.lowerSection.image (oppositePair E x y) = ⊤) :
    threeCore E x y = ⁅threeCore E x y, E.L₁⁆ ⊔ oppositePair E x y := by
  have h₃S : thirdLayer E x y ≤ threeCore E x y :=
    (d.series_inclusions hUT hf (d.L_le_I hUT hf)).2.2
  have h₃ := a.lowerSection.le_commutator_sup_of_coinvariants E.L₁
    (oppositePair E x y) (pointResidual_le_threeGroup E d hUT hf) hlower
  have h₄ := a.upperSection.le_commutator_sup_of_coinvariants E.L₁
    (⊥ : Subgroup G) (pointResidual_le_threeGroup E d hUT hf)
    (by rw [hupper, top_sup_eq])
  have h₃' : thirdLayer E x y ≤ ⁅threeCore E x y, E.L₁⁆ ⊔ oppositePair E x y :=
    h₃.trans (sup_le (sup_le ((commutator_mono h₃S le_rfl).trans le_sup_left)
      le_sup_right) ((triple_le_oppositePair E x y).trans le_sup_right))
  have hbound : threeCore E x y ≤ ⁅threeCore E x y, E.L₁⁆ ⊔ oppositePair E x y := by
    exact h₄.trans (sup_le (sup_le le_sup_left bot_le) h₃')
  exact le_antisymm hbound (sup_le
    (le_normalizer_iff_commutator_le_left.mp
      ((pointResidual_le_threeGroup E d hUT hf).trans (I_normalizes_core (setup E) x y)))
    (oppositePair_le_threeCore E d hUT hf))

/-- Fixed-point-free natural and dual layers put every X-fixed element in S₂. -/
theorem centralizer_le_triple (hX : LocalGeometry.IsCartan T L E.X)
    (hupper : ∀ v, (∀ z : E.X, a.upperAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0)
    (hlower : ∀ v, (∀ z : E.X, a.lowerAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0) :
    threeCore E x y ⊓ centralizer (E.X : Set G) ≤ triple E x y := by
  have hu := a.upperSection.centralizer_le_kernel E.X
    (Cartan_le_threeGroup E d hUT hf hX) hupper
  have hl := a.lowerSection.centralizer_le_kernel E.X
    (Cartan_le_threeGroup E d hUT hf hX) hlower
  exact (le_inf hu inf_le_right).trans hl

/-- The actual Cartan's odd order lifts the fixed-space calculation to generation in S. -/
theorem threeCore_le_of_fixed_calculations (hX : LocalGeometry.IsCartan T L E.X)
    (hupper : ∀ v, (∀ z : E.X, a.upperAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0)
    (hlower : ∀ v, (∀ z : E.X, a.lowerAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0) :
    threeCore E x y ≤ ⁅threeCore E x y, E.X⁆ ⊔ (threeCore E x y ⊓ E.W) := by
  have hp : IsPGroup 2 (threeCore E x y) := isPGroup_pCoreIn 2 _
  have hcop : Nat.Coprime (Nat.card E.X) (Nat.card (threeCore E x y)) := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hX.odd).pow_right n
  have hdec := eq_commutator_sup_centralizer_of_solvable_coprime (threeCore E x y) E.X
    ((Cartan_le_threeGroup E d hUT hf hX).trans (I_normalizes_core (setup E) x y))
    (@IsNilpotent.to_isSolvable _ _ hp.isNilpotent) hcop
  calc
    threeCore E x y = ⁅threeCore E x y, E.X⁆ ⊔
        (threeCore E x y ⊓ centralizer (E.X : Set G)) := hdec
    _ ≤ _ := sup_le_sup_left (le_inf inf_le_left
      ((a.centralizer_le_triple d hUT hf hX hupper hlower).trans (triple_le_closure E x y))) _

/-- The two upper calculations feed the actual core-containment and collapse consumer.
The lower-pair identity and earlier Chapter 11 conclusions retain their own owners. -/
theorem threeCore_collapse_of_layer_calculations
    (hX : LocalGeometry.IsCartan T L E.X)
    (hresUpper : Coinvariants.ker (a.upperAction.comp
      (inclusion (pointResidual_le_threeGroup E d hUT hf))) = ⊤)
    (hresLower : Coinvariants.ker (a.lowerAction.comp
      (inclusion (pointResidual_le_threeGroup E d hUT hf))) ⊔
        a.lowerSection.image (oppositePair E x y) = ⊤)
    (hfixUpper : ∀ v, (∀ z : E.X, a.upperAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0)
    (hfixLower : ∀ v, (∀ z : E.X, a.lowerAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hx : x ∈ normalizer (E.X : Set G)) (hy : y ∈ normalizer (E.X : Set G))
    (hUQ : E.W ≤ E.G₁.pCoreIn 2)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hEX : oppositePair E x y ≤ ⁅oppositePair E x y,E.X⁆ ⊔ triple E x y)
    (hcartan : ∀ P : Subgroup G, P ≤ (T : Subgroup G) → P = ⁅P,E.X⁆ →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hcoreX : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcentral : ⁅E.W,E.G₁.pCoreIn 2⁆ ≤ E.V₁) :
    threeCore E x y ≤ E.G₁.pCoreIn 2 ∧ threeCore E x y = triple E x y :=
  threeCore_collapse_of_generation E d hUT hf hTG hXG hX hx hy hUQ hgen
    (a.threeCore_eq_of_residual_calculations d hUT hf hresUpper hresLower)
    (a.threeCore_le_of_fixed_calculations d hUT hf hX hfixUpper hfixLower)
    hEX hcartan hcoreX hcentral

end UpperActions
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
