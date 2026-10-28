module

public import Theory.GroupTheory.CharacteristicTwoIndexTwoRestriction
public import Theory.GroupAction.NormalFiveTwentyBound
public import Theory.GroupTheory.ClassThreeNoFifteen
/-!
# A class-three residual bounds a characteristic-two quotient

Let a finite characteristic-two group have two-core of order 1024 and a
normal subgroup R of order 512, contained in a normal subgroup E of order
2560. Suppose R has class three, center of order two, and derived subgroup
equal to its Frattini subgroup of order 32. Then the quotient by the two-core
has order at most twenty.

The action on R/Φ(R) has two-group kernel, since R has index two in the
two-core. The image of E has order five and is normal in the full image.
The invariant third commutator excludes automorphisms of order fifteen on
R/Φ(R), so the normal-five bound makes the image order divide twenty.
The two-group kernel lies in the two-core, giving the result.

This packages the elementary group-action step used with the intrinsic
class-three group in Parrott, A characterization of the Tits' simple group
(1972), Lemma 1, and Thompson VI, printed pp.629--630.
-/

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
/-- A normal class-three residual controls the full quotient, even when
its order is half the order of the two-core. -/
public theorem quotient_card_le_twenty_of_normal_class_three_residual {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hQcard : Nat.card (pCore 2 G) = 1024)
    (R E : Subgroup G) [R.Normal] [E.Normal]
    (hRQ : R ≤ pCore 2 G) (hRE : R ≤ E)
    (hRcard : Nat.card R = 512) (hEcard : Nat.card E = 2560)
    (hclass : Group.nilpotencyClass R = 3) (hZ : Nat.card (center R) = 2)
    (hPhi : _root_.commutator R = frattini R) (hD : Nat.card (_root_.commutator R) = 32) :
    Nat.card (G ⧸ pCore 2 G) ≤ 20 := by
  let Q := pCore 2 G
  have hR : IsPGroup 2 R := pCore_isPGroup.to_le hRQ
  let _ : Fact (IsPGroup 2 R) := ⟨hR⟩
  let V := R ⧸ frattini R
  let _ : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let a : G →* MulAut V := (quotientAut (frattini R)).comp
    (MulAut.conjNormal : G →* MulAut R)
  let H := a.range
  let f : G →* H := a.rangeRestrict
  have hi : (R.subgroupOf Q).index = 2 := by
    have hh := (R.subgroupOf Q).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv, hRcard, hQcard] at hh
    omega
  have hkTwo : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact frattini_kernel_isPGroup_of_index_two_in_core hcentral R hRQ hi
  have hkQ : f.ker ≤ Q := le_sSup ⟨inferInstance, hkTwo⟩
  have hRk : R ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro r hr
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) v
    change quotientAut (frattini R) (MulAut.conjNormal r)
      (QuotientGroup.mk' (frattini R) x) = QuotientGroup.mk' (frattini R) x
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini R)
      ((⟨r, hr⟩ : R) * x * (⟨r, hr⟩ : R)⁻¹) = QuotientGroup.mk' (frattini R) x
    rw [map_mul, map_mul, map_inv, mul_comm (QuotientGroup.mk' (frattini R) (⟨r, hr⟩ : R))
      (QuotientGroup.mk' (frattini R) x), mul_inv_cancel_right]
  let T := f.ker.subgroupOf E
  have hTcard : Nat.card T = 512 := by
    have hdivQ : Nat.card T ∣ 1024 := by
      let j : T →* Q := (inclusion hkQ).comp {
        toFun := fun t => ⟨t.1.1, t.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
      have hj : Function.Injective j := by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun q : Q => (q : G)) h
      exact hQcard ▸ card_dvd_of_injective j hj
    have hdivE : Nat.card T ∣ 2560 := hEcard ▸ T.card_subgroup_dvd_card
    have hdiv : Nat.card T ∣ 512 := by simpa using Nat.dvd_gcd hdivQ hdivE
    have hge : 512 ≤ Nat.card T := by
      let j : R →* T := {
        toFun := fun r => ⟨⟨r, hRE r.property⟩, hRk r.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
      have hj : Function.Injective j := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun t : T => (t.1 : G)) h
      exact hRcard ▸ Nat.card_le_card_of_injective j hj
    exact Nat.le_antisymm (Nat.le_of_dvd (by decide) hdiv) hge
  let A := E.map f
  let _ : A.Normal := (inferInstance : E.Normal).map f a.rangeRestrict_surjective
  have hAcard : Nat.card A = 5 := by
    have hh := T.card_mul_index
    rw [hTcard, hEcard] at hh
    change 512 * f.ker.relIndex E = 2560 at hh
    rw [relIndex_ker] at hh
    change 512 * Nat.card A = 2560 at hh
    change Nat.card A = 5
    omega
  have hVcard : Nat.card V = 16 := by
    have hh := (frattini R).card_mul_index
    have hpc : Nat.card (frattini R) = 32 := hPhi ▸ hD
    rw [hpc, hRcard, index_eq_card] at hh
    change Nat.card V = 16
    change 32 * Nat.card V = 512 at hh
    omega
  have hno : ∀ h : H, orderOf h ≠ 15 := by
    intro h horder
    obtain ⟨g, hg⟩ := a.rangeRestrict_surjective h
    have ho := orderOf_injective H.subtype H.subtype_injective h
    rw [horder, ← hg] at ho
    exact ThirdCommutator.frattini_action_order_ne_fifteen hR hRcard hclass hZ hPhi hD
      (MulAut.conjNormal g) ho
  have hHdiv : Nat.card H ∣ 20 :=
    (normal_five_centralizer_and_card_bound H.subtype H.subtype_injective A hAcard hVcard hno).2
  have hHle : Nat.card H ≤ 20 := Nat.le_of_dvd (by decide) hHdiv
  have hkle : Nat.card f.ker ≤ 1024 := hQcard ▸ card_le_of_le hkQ
  have hcount := f.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr a.rangeRestrict_surjective, card_top] at hcount
  have hcore := Q.card_mul_index
  rw [hQcard, index_eq_card] at hcore
  change Nat.card (G ⧸ Q) ≤ 20
  nlinarith
end Subgroup
