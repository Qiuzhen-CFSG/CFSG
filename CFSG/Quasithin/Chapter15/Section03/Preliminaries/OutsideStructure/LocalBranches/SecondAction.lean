module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Coordinates

/-!
# The actual action in the second choice of 15.3.10

The proved cubic-coordinate calculation, applied to the earlier 15.3.7
image equality, gives [V,Y₊]=[V₂,Y₊]=V₂. Since V normalizes Y₊, this
places V₂ in O₂(Y₊). Its nontriviality supplies the missing two-local
normalizer control. Noncentrality also establishes S as a Sylow subgroup
of I before any core argument is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(1),(3) and the action used in (8),(9), pp.1123–1124.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
variable {G : Type*} [Group G] [Finite G]

/-- Both literal commutator identities in the second choice, from the
earlier full image and the proved compatible cubic-coordinate calculation. -/
theorem second_choice_commutator (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    ⁅d.V, d.Yplus⁆ = d.V₂ ∧ ⁅d.V₂, d.Yplus⁆ = d.V₂ := by
  have h := RankTwo.residualY_fullActionCoordinateFacts d.action h7image
  rw [hsecond.2]
  exact ⟨h.commutator 1 (Multiplicative.ofAdd (1 : ZMod 2)) (by decide),
    h.commutator_self 1 (Multiplicative.ofAdd (1 : ZMod 2)) (by decide)⟩

/-- The second plane lies in the two-core of the selected residual. -/
theorem second_choice_plane_le_core (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    d.V₂ ≤ d.Yplus.pCoreIn 2 := by
  have hVY : d.V ≤ normalizer (d.Yplus : Set G) :=
    ((v_le_s d).trans le_sup_right).trans (ys_normalizes_yplus d)
  have hle : d.V₂ ≤ d.Yplus := by
    rw [← (second_choice_commutator d hsecond h7image).1]
    exact le_normalizer_iff_commutator_le_right.mp hVY
  let _ := d.action.elementary_of_le (d.action.plane_le (Multiplicative.ofAdd (1 : ZMod 2)))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 d.V₂) hle
    ((choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice).trans (y_normalizes_plane d _))

/-- The nontrivial plane supplies the nontrivial-core premise for normalizer control. -/
theorem second_choice_core_ne_bot (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    d.Yplus.pCoreIn 2 ≠ ⊥ := by
  intro he
  exact plane_ne_bot d _ (le_bot_iff.mp (he ▸ second_choice_plane_le_core d hsecond h7image))

/-- All three ambient normalizer containments in (3), with their geometric
normalization and nontrivial-core premises discharged. -/
theorem second_choice_normalizers (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M ∧
      normalizer (d.Yplus : Set G) ≤ d.M := by
  have hp (i : OrthogonalPlaneIndex) : IsPGroup 2 (d.action.plane i) := by
    let _ := d.action.elementary_of_le (d.action.plane_le i)
    exact IsElementaryAbelian.isPGroup 2 _
  exact normalizers_of_second_choice d.Y d.S d.M d.V₁ d.V₂ d.Yplus hsecond.1
    (hp _) (plane_ne_bot d _) (hp _) (plane_ne_bot d _)
    (ys_normalizes_plane d _) (ys_normalizes_plane d _) (ys_normalizes_yplus d)
    (second_choice_core_ne_bot d hsecond h7image)

/-- The nontrivial commutator establishes noncentrality before the Sylow argument. -/
theorem second_choice_noncentral (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    ¬ d.Yplus ≤ centralizer (d.V : Set G) := by
  intro hc
  have he := (second_choice_commutator d hsecond h7image).1.symm.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  exact plane_ne_bot d _ he

/-- Noncentral action persists in U_I. If Y₊ centralized Z, normality of
Y₊ under Y would force it to centralize the earlier span V=⟨Z^Y⟩. -/
theorem second_choice_noncentral_ui (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V) :
    ¬ d.Yplus ≤ centralizer (d.UI I : Set G) := by
  intro hc
  have hZC : d.Z ≤ centralizer (d.Yplus : Set G) :=
    (le_conjugateSpanBy d.Z I).trans (le_centralizer_iff.mp hc)
  have hVC : d.V ≤ centralizer (d.Yplus : Set G) := by
    rw [← h7span]
    exact conjugateSpanBy_le hZC
      ((le_sup_left.trans (ys_normalizes_yplus d)).trans
        (normalizer_le_normalizer_centralizer d.Yplus))
  exact second_choice_noncentral d hsecond h7image (le_centralizer_iff.mp hVC)

/-- Clause (1) in the second choice, from the actual action and the earlier
15.3.2(4) and 15.3.6(2) outputs. -/
theorem second_choice_sylow (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hNS : normalizer (d.S : Set G) ≤ d.M)
    (h24 : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ d.M ⊓ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S := by
  exact lemma_15_3_11_1_of_action d.T d.M d.V d.Yplus d.S I d.sylow_le
    ((choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice).trans
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)) inf_le_left
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1) hNS d.action.normalizes
    h24 (chosen_residual_eq d.M d.Mc d.S d.V₁ d.Yplus d.choice)
    (second_choice_noncentral d hsecond h7image) hI

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
end
