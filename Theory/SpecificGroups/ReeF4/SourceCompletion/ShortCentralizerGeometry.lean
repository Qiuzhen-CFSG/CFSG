module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizer

/-!
# Preserving the native short involution class

Native two-class exhaustion and the actual centralizer distinction show that
automorphisms preserve the short class: short centralizers contain a perfect
PSL₂ subgroup, whereas long centralizers embed in a three-free Suzuki
parabolic. This retains the native short marker when choosing an extremal
conjugate in a full endpoint of an odd extension.

Exhaustion remains an explicit earlier-source premise. Source:
Aschbacher–Smith F.4.27,35,40, printed pp.288,292,294 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace ReeF4.SourceCompletion.ShortCentralizerGeometry
open EvenInvolutionGeometry Parabolics
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

/-- An automorphism preserves the short class once the two native involution
classes are exhausted. The distinction is detected by divisibility by three
in the actual centralizers, not by a class label. -/
theorem automorphism_preserves_short {m : ℕ} (hm : 0 < m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    (a : MulAut (Model m)) {t : Model m} (ht : IsShortRootInvolution t) :
    IsShortRootInvolution (a t) := by
  rcases hexhaust (a t) ((a.orderOf_eq t).trans (orderOf_of_isShortRootInvolution ht)) with hz | hs
  · obtain ⟨b,hb,hconj⟩ := hz
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    have hcard := Nat.card_congr
      (CentralizerSmallKernelTransport.centralizerEquiv a t).toEquiv
    have h3 : 3 ∣ Nat.card (centralizer ({a t} : Set (Model m))) :=
      hcard ▸ (short_centralizer_residual_three_dvd hm ht).trans (card_subgroup_dvd_card _)
    have hcard' := Nat.card_congr
      (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g)
        (longRootElement m b)).toEquiv
    change Nat.card (centralizer ({longRootElement m b} : Set (Model m))) =
      Nat.card (centralizer ({g * longRootElement m b * g⁻¹} : Set (Model m))) at hcard'
    rw [hg] at hcard'
    have hbound := long_centralizer_le_parabolic hm
      ((mem_longRootGroup m _).mpr ⟨b,rfl⟩) ((longRootElement_eq_one_iff m b).not.mpr hb)
    have hbad := (hcard'.symm ▸ h3).trans (card_dvd_of_le hbound)
    rw [←parabolic_eq_rootParabolic] at hbad
    exact (ConverseParabolics.suzuki_parabolic_three_free hm hbad).elim
  · exact hs

end ReeF4.SourceCompletion.ShortCentralizerGeometry
