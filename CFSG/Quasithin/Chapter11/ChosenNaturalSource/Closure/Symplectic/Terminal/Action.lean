module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Crossing
public import Theory.GroupTheory.SubgroupTransport
public import Theory.GroupTheory.SylowCoreRestriction

/-!
# The two original radical action images

The bars in the last line of 11.5.7 are images in Aut(V), obtained from
the actual normalizer action. We verify commutator transport for precisely
this map. The initial core bound puts W_H in R₁. After the plane rechoice,
A=[A,L₂] and A≤T put A in O₂(L₂), and hence in R₂.

The final model calculation is exposed separately: a nontrivial perfectly
moved subgroup of the R₂ image is its full L₂-displacement, which is not
contained in the R₁ image. This module proves the resulting contradiction
on the actual conjugate A, including all containment and kernel checks.
Source: Aschbacher--Smith 11.5.7, printed pp.783--784.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G]

/-- Monotonicity for the original normalizer action image. -/
theorem actionImage_mono {V A B : Subgroup G} (h : A ≤ B) :
    actionImage (V := V) A ≤ actionImage (V := V) B := map_mono (comap_mono h)

/-- Normalizer containments are essential: the image definition otherwise
only acts on the intersection with N_G(V). -/
theorem actionImage_commutator (V A B : Subgroup G)
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G)) :
    actionImage (V := V) ⁅A,B⁆ = ⁅actionImage (V := V) A,actionImage (V := V) B⁆ := by
  rw [actionImage, Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator A B hA hB,
    map_commutator]
  rfl

/-- The original action kernel is the literal centralizer of V. -/
theorem actionImage_eq_bot_iff (V A : Subgroup G)
    (hA : A ≤ normalizer (V : Set G)) :
    actionImage (V := V) A = ⊥ ↔ A ≤ centralizer (V : Set G) := by
  rw [actionImage, Subgroup.map_eq_bot_iff, normalizerMonoidHom_ker]
  constructor
  · intro h a ha
    exact h (show (⟨a,hA ha⟩ : normalizer (V : Set G)) ∈ A.subgroupOf _ from ha)
  · exact fun h => comap_mono h

variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The initial core bound gives containment in the actual R₁, not just a
family label or an abstractly isomorphic radical. -/
theorem closure_le_R₁ (m : MarkedFlag E) (hcore : E.W ≤ E.G₁.pCoreIn 2) :
    E.W ≤ E.R₁ := by
  exact hcore.trans (Theory.GroupTheory.pCoreIn_le_of_sylow_le T le_sup_right
    (sup_le ((residualIn_le _).trans inf_le_right) m.sylow_le_point_normalizer))

/-- Perfect movement forces the transported seed into the second radical. -/
theorem moved_seed_le_R₂ (m : MarkedFlag E) (A : Subgroup G)
    (hAT : A ≤ (T : Subgroup G)) (hmoved : ⁅A,E.L₂⁆ = A) : A ≤ E.R₂ := by
  have hT2 : (T : Subgroup G) ≤ normalizer (E.V₂ : Set G) := by
    rw [m.plane_preimage]
    exact m.flag.invariant 1
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₂ : Set G) :=
    LocalGeometry.sylow_normalizes_localResidual D E.V₂ hT2
  have hAL : A ≤ E.L₂ := hmoved.symm.le.trans
    (le_normalizer_iff_commutator_le_right.mp (hAT.trans hTL))
  have hLA : E.L₂ ≤ normalizer (A : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hmoved.le
  have hAC : A ≤ E.L₂.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hAT) hAL hLA
  have hn : E.L₂ ⊔ (T : Subgroup G) ≤ normalizer (E.L₂.pCoreIn 2 : Set G) :=
    (sup_le E.L₂.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image E.L₂ (pCore 2 E.L₂))
  exact hAC.trans (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 E.L₂)
    ((pCoreIn_le 2 _).trans le_sup_left) hn)

/-- The exact two assertions about the original radical images used in the
last line of the source proof. Neither field asserts a closure conclusion. -/
structure RadicalDisplacement : Prop where
  moved : ∀ B : Subgroup (MulAut V), B ≤ actionImage (V := V) E.R₂ →
    ⁅B,actionImage (V := V) E.L₂⁆ = B → B ≠ ⊥ →
      B = ⁅actionImage (V := V) E.R₂,actionImage (V := V) E.L₂⁆
  separated : ¬ ⁅actionImage (V := V) E.R₂,actionImage (V := V) E.L₂⁆ ≤
    actionImage (V := V) E.R₁

/-- The final contradiction compares the R₂ displacement and R₁ containment
for the very same subgroup A. -/
theorem false_of_moved_seed (m : MarkedFlag E) (r : RadicalDisplacement E)
    (A : Subgroup G) (hAR : A ≤ E.R₁)
    (hAN : A ≤ normalizer (V : Set G))
    (hmoved : ⁅A,E.L₂⁆ = A) (hne : ¬ A ≤ centralizer (V : Set G)) : False := by
  have hAT : A ≤ (T : Subgroup G) := hAR.trans
    (LocalGeometry.localRadical_le_sylow E.V₁)
  have hA2 := moved_seed_le_R₂ E m A hAT hmoved
  have hL2N : E.L₂ ≤ normalizer (V : Set G) :=
    ((residualIn_le _).trans inf_le_left).trans D.normalizes
  have he : ⁅actionImage (V := V) A,actionImage (V := V) E.L₂⁆ =
      actionImage (V := V) A := by
    rw [← actionImage_commutator V A E.L₂ hAN hL2N, hmoved]
  have hne' : actionImage (V := V) A ≠ ⊥ :=
    fun hb => hne ((actionImage_eq_bot_iff V A hAN).mp hb)
  exact r.separated ((r.moved _ (actionImage_mono hA2) he hne').symm.le.trans
    (actionImage_mono hAR))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
