module
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

/-!
# Removing the Frattini layer from a cubic residual image

A cubic image of the two-residual through a two-group kernel bounds the
residual of the original two-core quotient by three. Its order-six Frattini
quotient makes this residual nontrivial. The Frattini subgroup consequently
has two-power order and lies in the already trivial two-core.

This retains the literal source map used by the selected Baumann coordinate
in Stellmacher (2.4) and Aschbacher--Smith C.1.26, printed p.132.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {A : Type*} [Group A] [Finite A]

/-- A core-free three-by-two group whose Frattini quotient has order six
has trivial Frattini subgroup. This removes the Frattini layer of the
selected source SL₂(2) factor after its literal cubic image is computed. -/
theorem frattini_eq_bot_of_cubic_normal_and_six_quotient
    (hcore : pCore 2 A = ⊥) (R : Subgroup A) [R.Normal]
    (hR : Nat.card R = 3) (hQ : IsPGroup 2 (A ⧸ R))
    (hF : Nat.card (A ⧸ frattini A) = 6) : frattini A = ⊥ := by
  obtain ⟨n,hn⟩ := hQ.exists_card_eq
  have hmul := (frattini A).index_mul_card
  have htotal := R.index_mul_card
  change Nat.card (A ⧸ frattini A) * Nat.card (frattini A) = Nat.card A at hmul
  change Nat.card (A ⧸ R) * Nat.card R = Nat.card A at htotal
  rw [hF] at hmul
  rw [hn,hR] at htotal
  have htwo : 2 * Nat.card (frattini A) = 2^n := by omega
  have hp : IsPGroup 2 (frattini A) := IsPGroup.of_card_dvd_pow (n := n)
    ⟨2,by rw [←htwo,Nat.mul_comm]⟩
  exact le_bot_iff.mp ((le_sSup ⟨inferInstance,hp⟩ : frattini A ≤ pCore 2 A).trans_eq hcore)

/-- A literal cubic residual image through a two-group kernel removes the
Frattini layer above the two-core. -/
theorem residual_pCoreQuotient_card_of_cubic_image
    {X : Type*} [Group X] (q : A →* X) (hk : IsPGroup 2 q.ker)
    (hR : Nat.card ((pResidual 2 A).map q) = 3)
    (hF : Nat.card ((A ⧸ pCore 2 A) ⧸ frattini (A ⧸ pCore 2 A)) = 6) :
    Nat.card (pResidual 2 (A ⧸ pCore 2 A)) = 3 := by
  let Q := A ⧸ pCore 2 A
  let π : A →* Q := QuotientGroup.mk' (pCore 2 A)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkπ : π.ker = pCore 2 A := QuotientGroup.ker_mk' _
  have hle : q.ker ≤ π.ker := by
    rw [hkπ]
    exact le_sSup ⟨inferInstance,hk⟩
  have hd := relIndex_dvd_of_le_left (pResidual 2 A) hle
  rw [relIndex_ker,relIndex_ker,hR,map_pResidual_of_surjective 2 π hπ] at hd
  have hr : Nat.card (pResidual 2 Q) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | ht
    · have hb' : pResidual 2 Q = ⊥ := (card_eq_one).mp hb
      have hp : IsPGroup 2 Q := by
        have hh := isPGroup_quotient_pResidual (G := Q) 2
        exact hh.of_equiv ((QuotientGroup.quotientMulEquivOfEq hb').trans
          QuotientGroup.quotientBot)
      obtain ⟨n,hn⟩ := (hp.to_quotient (frattini Q)).exists_card_eq
      have hd3 : 3 ∣ 2^n := by rw [←hn,hF]; decide
      have hh := Nat.prime_three.dvd_of_dvd_pow hd3
      norm_num at hh
    · exact ht
  exact hr

/-- The Frattini layer above the original two-core is trivial. -/
theorem frattini_pCoreQuotient_eq_bot_of_cubic_image
    {X : Type*} [Group X] (q : A →* X) (hk : IsPGroup 2 q.ker)
    (hR : Nat.card ((pResidual 2 A).map q) = 3)
    (hF : Nat.card ((A ⧸ pCore 2 A) ⧸ frattini (A ⧸ pCore 2 A)) = 6) :
    frattini (A ⧸ pCore 2 A) = ⊥ := by
  let Q := A ⧸ pCore 2 A
  let π : A →* Q := QuotientGroup.mk' (pCore 2 A)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkπ : π.ker = pCore 2 A := QuotientGroup.ker_mk' _
  have hcore : pCore 2 Q = ⊥ := by
    have hc := π.comap_pCore_of_ker_isPGroup hπ (hkπ ▸ pCore_isPGroup)
    have hm := congrArg (map π) hc
    rw [map_comap_eq_self_of_surjective hπ] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr hkπ.ge)
  exact frattini_eq_bot_of_cubic_normal_and_six_quotient hcore
    (pResidual 2 Q) (residual_pCoreQuotient_card_of_cubic_image q hk hR hF)
    (isPGroup_quotient_pResidual 2) hF

end Theory.GroupTheory
