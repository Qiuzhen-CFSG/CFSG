module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.SecondChoice.Ordinary
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.SecondChoice.Selected

/-!
# The extraspecial second-choice core

The Sylow witness puts R=O₂(Y₊S) in S. Since Y₊ is normal in Y₊S,
[R,Y₊] lies in O₂(Y₊), so R fixes the selected elementary-nine quotient.
The proved faithful action of the actual four-group image of S then
forces R into the natural-action kernel C_T(V). The earlier YT core
calculation gives the reverse containment. No quotient recognition or
rank-two conclusion is used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the second-choice proof of 15.3.11(5i), printed p.1124.
-/

public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
open FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G] [Finite G]

/-- The extraspecial branch has exactly the earlier YT action kernel as its core. -/
theorem second_choice_extraspecial_core (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hsecond : OutsideStructure.SecondChoice d)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V)
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) := by
  let _ := h.extraspecial
  have hRS := chosen_core_le_s_of_sylow d I hI hSylow
  have hcomm : ⁅d.R, d.Yplus⁆ ≤ d.Yplus.pCoreIn 2 := by
    apply (commutator_core_le (d.Yplus ⊔ d.S) d.R d.Yplus le_sup_left
      ((d.Yplus ⊔ d.S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
      ((hRS.trans le_sup_right).trans (ys_normalizes_yplus d)) (isPGroup_pCoreIn 2 _)).2
  apply le_antisymm _ (centralizer_in_t_le_r d hcore)
  intro r hr
  let s : d.S := ⟨r, hRS hr⟩
  have hfix : selectedPlaneAction d hcore (selectedSylowProjection d s) = 1 := by
    apply MulEquiv.ext
    intro z
    obtain ⟨y, hy⟩ := z.property
    apply Subtype.ext
    change selectedSylowAction d hcore (selectedSylowProjection d s) (z : d.Y ⧸ pCore 2 d.Y) = z
    rw [← hy, selectedSylowAction_on_selected]
    let y' : d.Yplus := d.Yplus.normalizerMonoidHom
      ⟨s, ys_normalizes_yplus d (mem_sup_right s.property)⟩ y
    have hh : (y' * y⁻¹ : d.Yplus) ∈ pCore 2 d.Yplus := by
      obtain ⟨u, hu, he⟩ := hcomm (commutator_mem_commutator hr y.property)
      exact (Subtype.ext he : u = y' * y⁻¹) ▸ hu
    have he : selectedQuotientMap d (y' * y⁻¹) = 1 :=
      (selectedQuotientMap_kernel d (IsExtraspecial.isPGroup 3 _)).ge hh
    rw [map_mul, map_inv, mul_inv_eq_one] at he
    exact he
  have hs : selectedSylowProjection d s = 1 :=
    (selectedPlaneAction_injective d hsecond hcore h7image h)
      (hfix.trans (map_one _).symm)
  have ha : (⟨r, d.sylow_le s.property.1⟩ : d.M) ∈ d.action.actor.ker :=
    congrArg Subtype.val hs
  rw [d.action.ker_actor] at ha
  exact ⟨s.property.1, ha⟩

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

end
