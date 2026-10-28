module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Layers.Residual

/-!
# The opposite-pair fixed-space lift and the original collapse consumer

The source opposite pair lies in S₃ and is normalized by the actual Cartan.
Its Cartan centralizer therefore lies in S₂ whenever the lower quotient has
zero common fixed space. Coprime decomposition proves its generation identity.
Together with the proved residual calculations, this supplies all three inputs
to the original core-containment and collapse theorem.

The final owner `qt-d-1222-sl3-layer-generation` still must construct the
natural and dual models and discharge both Cartan fixed-space premises.
The earlier Chapter 11 core and Cartan hypotheses retain their source owners.

Source: Aschbacher--Smith, 11.5.7, printed pp.781--782.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open ChapterG.Section02.LinearThree
open Recognition
open scoped IsMulCommutative
attribute [local instance] ZMod.algebra

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Geometry D} {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
  (hUT : E.W ≤ (T : Subgroup G))
  (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
  [((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal]
  [((triple E x y).subgroupOf (thirdLayer E x y)).Normal]
  [IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y))]
  [IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y))]

local instance fixedUpperNormal :
    ((S₃ (setup E) x y).subgroupOf (S (setup E) x y)).Normal :=
  inferInstanceAs (((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal)
local instance fixedLowerNormal :
    ((S₂ (setup E) x y).subgroupOf (S₃ (setup E) x y)).Normal :=
  inferInstanceAs (((triple E x y).subgroupOf (thirdLayer E x y)).Normal)
local instance fixedUpperElementary : IsElementaryAbelian 2 (UpperQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y)))
local instance fixedLowerElementary : IsElementaryAbelian 2 (LowerQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y)))

namespace UpperActions
variable (a : UpperActions E x y)

/-- Coprime action lifts the lower fixed-space calculation to the literal opposite pair. -/
theorem oppositePair_le_of_fixed_calculation
    (hX : LocalGeometry.IsCartan T L E.X) (hXG : E.X ≤ E.G₁)
    (hx : x ∈ normalizer (E.X : Set G)) (hy : y ∈ normalizer (E.X : Set G))
    (hfix : ∀ v, (∀ z : E.X, a.lowerAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0) :
    oppositePair E x y ≤ ⁅oppositePair E x y, E.X⁆ ⊔ triple E x y := by
  have hp : IsPGroup 2 (oppositePair E x y) :=
    (isPGroup_pCoreIn 2 (threeGroup E x y)).to_le
      (oppositePair_le_threeCore E d hUT hf)
  have hdec := eq_commutator_sup_centralizer_of_solvable_coprime (oppositePair E x y) E.X
    (Cartan_normalizes_oppositePair E hXG hx hy)
    (@IsNilpotent.to_isSolvable _ _ hp.isNilpotent)
    (Cartan_coprime_oppositePair E x y hUT hX)
  have hfixed := a.lowerSection.centralizer_le_kernel E.X
    (Cartan_le_threeGroup E d hUT hf hX) hfix
  calc
    oppositePair E x y = ⁅oppositePair E x y, E.X⁆ ⊔
        (oppositePair E x y ⊓ centralizer (E.X : Set G)) := hdec
    _ ≤ _ := sup_le_sup_left
      ((inf_le_inf_right _ (oppositePair_le_thirdLayer E d hUT hf)).trans hfixed) _

/-- Apply all three generation identities to the original collapse consumer.
The two models and their Cartan fixed-space calculations remain explicit. -/
theorem threeCore_collapse_of_models_and_fixed_spaces {r s : ℕ}
    (upper : NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r)
    (lower : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hfixUpper : ∀ v, (∀ z : E.X, a.upperAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0)
    (hfixLower : ∀ v, (∀ z : E.X, a.lowerAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) → v = 0)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hx : x ∈ normalizer (E.X : Set G)) (hy : y ∈ normalizer (E.X : Set G))
    (hUQ : E.W ≤ E.G₁.pCoreIn 2)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hcartan : ∀ P : Subgroup G, P ≤ (T : Subgroup G) → P = ⁅P,E.X⁆ →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hcoreX : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcentral : ⁅E.W,E.G₁.pCoreIn 2⁆ ≤ E.V₁) :
    threeCore E x y ≤ E.G₁.pCoreIn 2 ∧ threeCore E x y = triple E x y :=
  threeCore_collapse_of_generation E d hUT hf hTG hXG hX hx hy hUQ hgen
    (a.threeCore_eq_of_homogeneous_layers d hUT hf upper lower)
    (a.threeCore_le_of_fixed_calculations d hUT hf hX hfixUpper hfixLower)
    (a.oppositePair_le_of_fixed_calculation d hUT hf hX hXG hx hy hfixLower)
    hcartan hcoreX hcentral

end UpperActions
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
