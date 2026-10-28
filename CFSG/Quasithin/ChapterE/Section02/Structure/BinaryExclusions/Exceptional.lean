module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.IntrinsicTwoParabolics
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoPowerStability
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.SeedGeneration
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.Stabilizers
public import Theory.SpecificGroups.Tits.FiniteSimple
/-!
# Exceptional binary normal supplements are not minimal parabolic

The actual triality, Ree and Tits carriers have two proper generating
parabolics containing their marked Sylow two-subgroup. The ambient Sylow
normalizes each after conjugating the model marking to its intersection
with the normal subgroup. The Ree argument retains the two-power order of
that action, exactly the hypothesis of its concrete parabolic theorem.

Source: Aschbacher–Smith E.2.2, printed p.216, the characteristic-two
normal-component case. No module classification or recognition premise is
used; each parabolic and its Sylow marking is the concrete model subgroup.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.BinaryExclusions
variable {H : Type*} [Group H] [Finite H]
theorem not_minimalParabolic_of_triality
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (P : Triality.Standard.Parameters) (hp : P.prime = 2)
    (e : K ≃* Triality.Standard.Carrier P) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  open Triality.Standard.Parabolics in
  exact ChapterB.not_minimalParabolic_of_intrinsic_parabolics T K e hgen
    (unipotentSylow P hp) (parabolic P .arms) (parabolic P .central)
    (parabolic_sup_binary P hp) (parabolic_ne_top_binary P hp .arms)
    (parabolic_ne_top_binary P hp .central)
    ((unipotent_le_borel P).trans (borel_le_parabolic P .arms))
    ((unipotent_le_borel P).trans (borel_le_parabolic P .central))
    (fun a ha => ⟨parabolic_map_eq_of_unipotent_invariant P hp .arms a ha,
      parabolic_map_eq_of_unipotent_invariant P hp .central a ha⟩)

theorem not_minimalParabolic_of_ree
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (m : ℕ) (hm : 1 ≤ m) (e : K ≃* ReeF4.Model m) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  open ReeF4.ConverseParabolics ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry in
  obtain ⟨U,hU⟩ := exists_sylow_eq_unipotent m
  have hjoin : parabolic m .suzuki ⊔ parabolic m .linear = ⊤ := by
    rw [parabolic_eq_rootParabolic, parabolic_eq_rootParabolic]
    apply top_unique
    rw [← ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.seed_sup_eq_top m]
    exact sup_le_sup (ReeF4.Parabolics.seed_le_parabolic m .suzuki)
      (ReeF4.Parabolics.seed_le_parabolic m .linear)
  apply ChapterB.not_minimalParabolic_of_twoPower_parabolics T K e hgen U
    (parabolic m .suzuki) (parabolic m .linear) hjoin
    ((octagonGeometry m hm).parabolic_ne_top .suzuki)
    ((octagonGeometry m hm).parabolic_ne_top .linear)
  · rw [hU]
    exact unipotent_le_parabolic m .suzuki
  · rw [hU]
    exact unipotent_le_parabolic m .linear
  · intro a ha hau
    rw [hU] at hau
    have hi : ∀x, x∈unipotent m ↔ a x∈unipotent m := by
      intro x
      have hx := mem_map_iff_mem (f := a.toMonoidHom) a.injective
        (K := unipotent m) (x := x)
      rw [hau] at hx
      exact hx.symm
    have hj := parabolic_invariant_of_twoPower hm a ha hi
    have he (s) : (parabolic m s).map a.toMonoidHom = parabolic m s := by
      ext x
      rw [mem_map_equiv]
      simpa only [MulEquiv.apply_symm_apply] using hj s (a.symm x)
    exact ⟨he .suzuki,he .linear⟩

theorem not_minimalParabolic_of_tits
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : K ≃* Tits.ParrottGroup) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  open Tits Tits.ExceptionalParabolics in
  have hp : first ≠ ⊤ := by
    intro he
    have hc := first_card
    rw [he, Nat.card_congr Subgroup.topEquiv.toEquiv, atlas1600Group_card] at hc
    omega
  have hq : second ≠ ⊤ := by
    intro he
    have hc := second_card
    rw [he, Nat.card_congr Subgroup.topEquiv.toEquiv, atlas1600Group_card] at hc
    omega
  apply ChapterB.not_minimalParabolic_of_intrinsic_parabolics T K
    (e.trans parrottFiniteImageEquiv) hgen atlas1600SylowTwo first second generate hp hq
  · simpa only [atlas1600SylowTwo_coe] using sylow_le_first
  · simpa only [atlas1600SylowTwo_coe] using sylow_le_second
  · intro a ha
    rw [atlas1600SylowTwo_coe] at ha
    exact ⟨RelativeParabolicNormalizers.first_stabilized a ha,
      RelativeParabolicNormalizers.second_stabilized a ha⟩
end CFSG.Quasithin.ChapterE.BinaryExclusions
