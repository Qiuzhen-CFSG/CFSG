module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.ExtraspecialGeometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components

/-!
# The moved-space action in 14.4.8(2)

The earlier extraspecial geometry forces V₂ into VX and identifies the I₂
image with its hyperplane stabilizer. X escapes that stabilizer, giving the
full LXT action. Residual functoriality gives the full LX action. Selection
then constructs a faithful local component and applies the universal earlier
14.3.4 implication. The actual action excludes A₅, and the marked projection
places both generators in the selected PSL₃(2) component. Its quotient now
identifies both action kernels with their two-cores.

The final theorem assembles these arguments without assuming a full action,
component placement, faithful-family membership, or a core quotient. Its
remaining hypotheses are the explicit earlier 12.8/14.3 clauses and 1.2.1(1).
They are to be supplied in the genuine Hypothesis 14.3.10 configuration by
the outer source owner, in the extraspecial d > 4 branch. This is not a new
encoding of that hypothesis. Whole-parabolic recognition is supplied by the
separate SourceFlags branch; I₂ is kept distinct from I₂T = L₂T.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, printed p.1009.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
open ChapterA.Section04 Components

variable {G : Type*} [Group G] [Finite G]

/-- The constructed action and component conclusions, with all maps marked
by actual ambient conjugation. This is an output of `full_moved_space_action`,
not a hypothesis replacing the source argument. -/
structure FullMovedSpaceAction (T : Sylow 2 G) (I₂ L₂ V₂ X : Subgroup G) where
  plane_le : V₂ ≤ movedSpace V₂ X
  I₂_normalizes : I₂ ≤ normalizer (movedSpace V₂ X : Set G)
  I₂_image : (conjugation I₂ (movedSpace V₂ X) I₂_normalizes).range =
    MulAction.stabilizer (MulAut (movedSpace V₂ X))
      (V₂.subgroupOf (movedSpace V₂ X))
  I₂_image_maximal : IsCoatom (conjugation I₂ (movedSpace V₂ X) I₂_normalizes).range
  member_escapes : ¬ (conjugation X (movedSpace V₂ X)
    (member_normalizes_movedSpace V₂ X)).range ≤
      MulAction.stabilizer (MulAut (movedSpace V₂ X))
        (V₂.subgroupOf (movedSpace V₂ X))
  normalizes : localJoin L₂ X ⊔ (T : Subgroup G) ≤
    normalizer (movedSpace V₂ X : Set G)
  surjective : Function.Surjective
    (conjugation (localJoin L₂ X ⊔ (T : Subgroup G)) (movedSpace V₂ X) normalizes)
  local_surjective : Function.Surjective
    (conjugation (localJoin L₂ X) (movedSpace V₂ X) (le_sup_left.trans normalizes))
  kernel : (conjugation (localJoin L₂ X ⊔ (T : Subgroup G))
    (movedSpace V₂ X) normalizes).ker =
      pCore 2 (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G)
  local_kernel : (conjugation (localJoin L₂ X) (movedSpace V₂ X)
    (le_sup_left.trans normalizes)).ker = pCore 2 (localJoin L₂ X)
  component : localJoin L₂ X ∈ Chapter1.cComponentsIn (localJoin L₂ X)
  maximal : localJoin L₂ X ∈ Chapter1.LStar G T
  faithful : IsFaithfulSignalizerType (localJoin L₂ X)
  L₂_commutator : L₂ = ⁅L₂, (T : Subgroup G) ⊓ localJoin L₂ X⁆
  X_commutator : X = ⁅X, (T : Subgroup G) ⊓ localJoin L₂ X⁆
  glModel : MulAut (movedSpace V₂ X) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)
  pslModel : MulAut (movedSpace V₂ X) ≃* Matrix.PSL3Two.PSL
  localQuotient : coreQuotient (localJoin L₂ X) ≃* Matrix.PSL3Two.PSL
  localQuotient_mk : ∀ a : localJoin L₂ X,
    localQuotient (QuotientGroup.mk' (pCore 2 (localJoin L₂ X)) a) =
      pslModel (conjugation (localJoin L₂ X) (movedSpace V₂ X)
        (le_sup_left.trans normalizes) a)
  quotient : coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃* Matrix.PSL3Two.PSL
  quotient_mk : ∀ a : (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G),
    quotient (QuotientGroup.mk'
      (pCore 2 (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G)) a) =
      pslModel (conjugation (localJoin L₂ X ⊔ (T : Subgroup G))
        (movedSpace V₂ X) normalizes a)
  glQuotient : coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃*
    Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)
  glQuotient_mk : ∀ a : (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G),
    glQuotient (QuotientGroup.mk'
      (pCore 2 (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G)) a) =
      glModel (conjugation (localJoin L₂ X ⊔ (T : Subgroup G))
        (movedSpace V₂ X) normalizes a)

/-- Assemble the action and component argument of 14.4.8(2) for every
literal Y-member. The plane action and supplement are 12.8.9(1--2),
elementarity and the fixed-space pullback are 12.8.11(2),(4), and the
central lines and commutator bounds are the extraspecial case of 12.8.8(1).
The L₂ premises are the earlier cubic parabolic residual facts. The outer
source assembly retains discharge of these earlier inputs, condition (E),
1.2.1(1), and the universal 14.3.4(1--2) implication. -/
theorem full_moved_space_action
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {H V₂ E X U Ug Z Zg Wg L₂ : Subgroup G} [IsElementaryAbelian 2 E]
    (hX : X ∈ YFamily H T V₂ E)
    (hV₂T : V₂ ≤ T) (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hUT : U ≤ T) (hWgT : Wg ≤ T) (hWgUg : Wg ≤ Ug)
    (hE : E ≤ U ⊓ Ug)
    (hU : ⁅U,U⁆ ≤ Z) (hUg : ⁅Ug,Ug⁆ ≤ Zg)
    (hZU : U ⊓ centralizer (U : Set G) = Z)
    (hZ : Nat.card Z = 2) (hZg : Nat.card Zg = 2) (hV₂ : Nat.card V₂ = 4)
    (hplane : V₂ = Z ⊔ Zg)
    (hfixed : ∀ D : Subgroup G, D ≤ E → ⁅D,Wg⁆ ≤ Z → D ≤ V₂)
    (hI : U ⊔ Ug = L₂ ⊔ U)
    (hIP : U ⊔ Ug ≤ normalizer (V₂ : Set G))
    (hSix : Nat.card (conjugation (U ⊔ Ug) V₂ hIP).range = 6)
    (hWgP : Wg ≤ centralizer (V₂ : Set G))
    (hL₂ : twoResidual L₂ = L₂) (hLc : Nat.card (coreQuotient L₂) = 3)
    (hTL₂ : (T : Subgroup G) ≤ normalizer (L₂ : Set G)) :
    Nonempty (FullMovedSpaceAction T (U ⊔ Ug) L₂ V₂ X) := by
  let : IsElementaryAbelian 2 (movedSpace V₂ X) := IsElementaryAbelian.of_le hX.2.2
  obtain ⟨hVW, hIW, himage, hmax, hn, hs⟩ :=
    full_conjugation_of_earlier_extraspecial_data hX hTV₂ hUT hWgT hWgUg
      hE hU hUg hZU hZ hZg hV₂ hplane hfixed hI hIP hSix hWgP
  obtain ⟨S⟩ := exists_selectedComponent_of_full_join_action earlier T hEven
    classification hX hV₂T hL₂ hTL₂ hn hs
  obtain ⟨hcommL, hcommX, _, _, heq⟩ :=
    selectedComponent_eq_localJoin T hX hL₂ hLc hTL₂ hn S
  have hquot : Nonempty (coreQuotient (localJoin L₂ X) ≃* Matrix.PSL3Two.PSL) :=
    heq ▸ S.quotient
  have hsL := localJoin_action_surjective_of_join_T hX hL₂ hTL₂ T.isPGroup' hn hs
  have hkL := kernel_eq_core_of_full_action_and_quotient hX.2.1 _ hsL hquot.some
  have hk := localJoin_join_T_action_kernel hX hL₂ hTL₂ T.isPGroup' hn hs hquot.some
  obtain ⟨eGL⟩ := elementaryEight_mulAut_equiv_GL (movedSpace V₂ X) hX.2.1
  obtain ⟨ePSL⟩ := MulAut.elementaryEight_equiv_PSL3 hX.2.1
  exact ⟨{
    plane_le := hVW
    I₂_normalizes := hIW
    I₂_image := himage
    I₂_image_maximal := hmax
    member_escapes := member_image_not_le_plane_stabilizer hX hV₂ hVW
    normalizes := hn
    surjective := hs
    local_surjective := hsL
    kernel := hk
    local_kernel := hkL
    component := Eq.subst
      (motive := fun C : Subgroup G => C ∈ Chapter1.cComponentsIn (localJoin L₂ X))
      heq.symm S.component
    maximal := heq ▸ S.maximal
    faithful := heq ▸ S.faithful
    L₂_commutator := heq ▸ hcommL
    X_commutator := heq ▸ hcommX
    glModel := eGL
    pslModel := ePSL
    localQuotient := (coreConjugationEquiv _ _ (le_sup_left.trans hn) hsL hkL).trans ePSL
    localQuotient_mk := fun a => congrArg ePSL
      (coreConjugationEquiv_mk _ _ (le_sup_left.trans hn) hsL hkL a)
    quotient := (coreConjugationEquiv _ _ hn hs hk).trans ePSL
    quotient_mk := fun a => congrArg ePSL (coreConjugationEquiv_mk _ _ hn hs hk a)
    glQuotient := (coreConjugationEquiv _ _ hn hs hk).trans eGL
    glQuotient_mk := fun a => congrArg eGL (coreConjugationEquiv_mk _ _ hn hs hk a) }⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
