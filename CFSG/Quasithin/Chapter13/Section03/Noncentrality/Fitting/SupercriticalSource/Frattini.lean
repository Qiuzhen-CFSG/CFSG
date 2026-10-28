module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Source
public import Theory.GroupAction.QuaternionPrimePlane

/-!
# Quaternion irreducibility on the selected Frattini plane

Each genuine Ξ odd quotient has Frattini quotient of order p². The
Burnside basis kernel is a p-group, so a faithful quaternion action stays
faithful on that quotient for odd p. The actual quaternion prime-plane
calculation then gives irreducibility without assuming it.

Source: Aschbacher–Smith 13.3.14(d), printed p.892.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

variable {p : ℕ} [Fact p.Prime] {D : Type*} [Group D] [Finite D]

theorem xiOdd_frattini_card (hD : Chapter1.XiOddQuotient p D) :
    Nat.card (D ⧸ frattini D) = p ^ 2 := by
  let : Fact (IsPGroup p D) := ⟨hD.isPGroup⟩
  rcases hD with ⟨he, hc⟩ | ⟨he, hc, _⟩
  · let : IsElementaryAbelian p D := he
    rw [frattini_eq_bot_of_isElementaryAbelian (p := p)]
    exact (Nat.card_congr (QuotientGroup.quotientBot : (D ⧸ (⊥ : Subgroup D)) ≃* D).toEquiv).trans hc
  · let : IsExtraspecial p D := he
    have hphi : Nat.card (frattini D) = p := by
      rw [IsExtraspecial.frattini_eq_center (p := p), IsExtraspecial.center_order_p p D]
    have hh := (frattini D).index_mul_card
    change Nat.card (D ⧸ frattini D) * Nat.card (frattini D) = Nat.card D at hh
    rw [hphi, hc, show 3 = 2 + 1 from rfl, pow_succ] at hh
    exact mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hh

theorem faithful_quaternion_frattini_irreducible
    (hp : Odd p) (hD : Chapter1.XiOddQuotient p D)
    (f : QuaternionGroup 2 →* MulAut D) (hf : Function.Injective f)
    (A : Subgroup (D ⧸ frattini D))
    (hA : ∀ g x, x ∈ A → quotientAut (frattini D) (f g) x ∈ A) : A = ⊥ ∨ A = ⊤ := by
  let : Fact (IsPGroup p D) := ⟨hD.isPGroup⟩
  let : IsElementaryAbelian p (D ⧸ frattini D) := isElementaryAbelian_quotient_frattini
  let a := (quotientAut (frattini D)).comp f
  have hk : IsPGroup p a.ker :=
    (isPGroup_quotientAut_frattini_kernel hD.isPGroup).comap_of_injective f hf
  have htwo : IsPGroup 2 (QuaternionGroup 2) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_eq_fintype_card]; norm_num [QuaternionGroup.card])
  have hd := (htwo.to_subgroup a.ker).disjoint_of_coprime hk (Nat.coprime_two_left.mpr hp)
  have hai : Function.Injective a := (MonoidHom.ker_eq_bot_iff a).mp
    (by simpa only [disjoint_self] using hd)
  exact QuaternionGroup.faithful_plane_irreducible hp (xiOdd_frattini_card hD) a hai A hA

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
