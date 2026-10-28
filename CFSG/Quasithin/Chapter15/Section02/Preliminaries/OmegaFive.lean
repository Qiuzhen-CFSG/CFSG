module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions.Nilpotent
public import Theory.GroupTheory.CyclicNormalCentralizer

/-!
# An invariant subgroup of order five in the nilpotent omega layer

Let K be a finite perfect group in the nilpotent alternative of A.3.6.
An S-invariant subgroup Y of order five in P = Ω₁(O₅(K)), for an actual
Sylow two-subgroup S of K, has trivial image in P/Φ(P): the action is
irreducible and the quotient has order twenty-five. Thus Y lies in Φ(P).
If P is elementary abelian this is impossible. Otherwise P has order 125,
so Φ(P) has order five. Its ambient image is characteristic in K and cyclic;
perfectness of K therefore makes it central, and hence Y is central.

This repairs the nilpotent step in the proof of Aschbacher--Smith 15.2.4,
printed p.1107, without asserting that the full five-core is elementary or
discarding higher homocyclic exponents. The actual quotient and Sylow
transport, and normalization of the preimage in the source configuration,
remain separate inputs to the section's assembly.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions

namespace CFSG.Quasithin.Chapter15.Section02.OmegaFive

variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Irreducibility of the actual Sylow action forces the order-five subgroup
into the ambient image of the omega layer's Frattini subgroup. -/
theorem invariant_five_le_omega_frattini
    (hnil : A36Nilpotent K) (hfive : 5 ∣ Nat.card (fittingSubgroup K))
    (S : Sylow 2 K) (Y : Subgroup K) (hY : Nat.card Y = 5)
    (hYP : Y ≤ omegaCore 5 K) (hSY : (S : Subgroup K) ≤ normalizer (Y : Set K)) :
    Y ≤ (frattini (omegaCore 5 K)).map (omegaCore 5 K).subtype := by
  let P := omegaCore 5 K
  let U := Y.subgroupOf P
  let q := QuotientGroup.mk' (frattini P)
  have hU : Nat.card U = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hYP).toEquiv).trans hY
  have hinv : ∀ (s : S) a, a ∈ U.map q → omegaFrattiniAction 5 K s a ∈ U.map q := by
    rintro s a ⟨u, hu, rfl⟩
    refine ⟨omegaCoreAction 5 K s u, ?_, ?_⟩
    · change ((omegaCoreAction 5 K s u : P) : K) ∈ Y
      rw [omegaCoreAction_apply]
      exact (mem_normalizer_iff.mp (hSY s.property) u).mp hu
    · dsimp only [q, P, omegaFrattiniAction, MonoidHom.comp_apply]
      rw [quotientAut_apply_mk]
  have hzero : U.map q = ⊥ := by
    rcases (CenterFrattiniSource.nilpotent_sylow_actions hnil (by decide) hfive S).1
        (U.map q) hinv with hzero | htop
    · exact hzero
    · have hd := U.card_map_dvd q
      have hquot := (Nilpotent.frattini_shape hnil hfive).2
      rw [htop, card_top, hU] at hd
      change Nat.card (omegaCore 5 K ⧸ frattini (omegaCore 5 K)) ∣ 5 at hd
      rw [hquot] at hd
      norm_num at hd
  have hUphi : U ≤ frattini P := by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff U).mp hzero
  intro y hy
  exact ⟨⟨y, hYP hy⟩, hUphi hy, rfl⟩

/-- The nilpotent A.3.6 alternative centralizes every Sylow-invariant subgroup
of order five in its actual first five-core omega layer. -/
theorem invariant_five_le_center
    (hnil : A36Nilpotent K) (hfive : 5 ∣ Nat.card (fittingSubgroup K))
    (S : Sylow 2 K) (Y : Subgroup K) (hY : Nat.card Y = 5)
    (hYP : Y ≤ omegaCore 5 K) (hSY : (S : Subgroup K) ≤ normalizer (Y : Set K)) :
    Y ≤ center K := by
  let P := omegaCore 5 K
  let N := (frattini P).map P.subtype
  have hYN : Y ≤ N := invariant_five_le_omega_frattini hnil hfive S Y hY hYP hSY
  have hshape : XiOddQuotient 5 P :=
    ((RadicalStructure.core_omega (Or.inr hnil) hfive).2).of_mulEquiv
      ((omega (pCore 5 K) (p := 5) 1).equivMapOfInjective
        (pCore 5 K).subtype (pCore 5 K).subtype_injective)
  rcases hshape with ⟨he, _⟩ | ⟨_, hP, _⟩
  · let := he
    let : Fact (IsPGroup 5 P) := ⟨IsElementaryAbelian.isPGroup 5 P⟩
    have hN : N = ⊥ := by
      dsimp only [N]
      rw [frattini_eq_bot_of_isElementaryAbelian (p := 5), Subgroup.map_bot]
    have hYbot : Y = ⊥ := bot_unique (hN ▸ hYN)
    rw [hYbot, card_bot] at hY
    norm_num at hY
  · have hphi : Nat.card (frattini P) = 5 := by
      have hc := card_eq_card_quotient_mul_card_subgroup (frattini P)
      have hquot : Nat.card (P ⧸ frattini P) = 5 ^ 2 :=
        (Nilpotent.frattini_shape hnil hfive).2
      rw [hP, hquot] at hc
      omega
    let : N.Characteristic := characteristic_of_characteristic_of_characteristic
    let : IsCyclic N := isCyclic_of_prime_card (p := 5) (by
      dsimp only [N]
      rw [card_map_of_injective P.subtype_injective, hphi])
    have hcentral : (⊤ : Subgroup K) ≤ centralizer (N : Set K) := by
      simpa only [Group.IsPerfect.commutator_eq_top] using
        commutator_le_centralizer_of_isCyclic_normal N
    have hNcenter : N ≤ center K := by
      simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp hcentral
    exact hYN.trans hNcenter

end CFSG.Quasithin.Chapter15.Section02.OmegaFive
