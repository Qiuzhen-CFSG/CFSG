module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Residual
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# Large-prime factors permuting with the binary derived Sylow

Every nontrivial p-subgroup for p>3 lies in the actual derived group, and
its order forces p=7. A permuting product with a two-group containing the
derived Sylow therefore contains the whole derived group, by the checked
seven-overgroup theorem. This contradicts the absence of three in the
product order. The proof reuses root-word certificates without adding a
new enumeration or assuming a subgroup catalogue.

Source application: Aschbacher–Smith12.2.11(c), pp.798–799, the claim
that the original odd Hall p-subgroup centralizes the natural unitary module.
-/

public section
open Subgroup
open scoped Pointwise
namespace Atlas.G2.BinaryLargePrimeSylow
open BinaryParabolicPair
local notation "D" => commutator (Model (ZMod 2))
local notation "G" => Model (ZMod 2)
/-- A p-group with p>3 permuting with a two-group containing the actual
derived Sylow is trivial. No solvability or normality of the factors is used. -/
theorem permutable_prime_eq_bot {p:ℕ} [Fact p.Prime] (hp:3<p) (B S:Subgroup G)
    (hB:IsPGroup p B) (hS:IsPGroup 2 S)
    (hP:derivedSylowAmbient≤S)
    (hperm:(B:Set G)*(S:Set G)=(S:Set G)*(B:Set G)) : B=⊥ := by
  have hcop:Nat.Coprime p 2:=(Fact.out:Nat.Prime p).coprime_iff_not_dvd.mpr (by
    intro h;have := Nat.le_of_dvd (by decide:0<2) h;omega)
  have hBD:B≤D := by
    rw [←EvenFieldFixedResidual.binary_twoResidual_eq_commutator]
    intro b hb
    apply mem_pResidual_of_orderOf_coprime
    have hh:=hB.orderOf_coprime hcop (⟨b,hb⟩:B)
    rw [←Subgroup.orderOf_coe] at hh
    exact hh.symm
  by_contra hn
  have hpB:p∣Nat.card B:=hB.card_eq_or_dvd.resolve_left (by
    have hh:=B.one_lt_card_iff_ne_bot.mpr hn
    omega)
  have hpD:p∣6048:= by
    have hh:=hpB.trans (card_dvd_of_le hBD)
    rwa [DerivedEvenOrder.card_derived_binary (by simp)] at hh
  have hp7:p=7 := by
    rw [show 6048=2^5*(3^3*7) from rfl] at hpD
    rcases (Fact.out:Nat.Prime p).dvd_mul.mp hpD with h|h
    · have hd: p∣2:=(Fact.out:Nat.Prime p).dvd_of_dvd_pow h
      have := Nat.le_of_dvd (by decide:0<2) hd;omega
    · rcases (Fact.out:Nat.Prime p).dvd_mul.mp h with h|h
      · have hd:p∣3:=(Fact.out:Nat.Prime p).dvd_of_dvd_pow h
        have := Nat.le_of_dvd (by decide:0<3) hd;omega
      · exact (Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp h
  subst p
  let K:=B⊔S
  have h7:7∣Nat.card (K.subgroupOf D) := by
    have hcard:Nat.card (B.subgroupOf D)=Nat.card B:=
      Nat.card_congr (subgroupOfEquivOfLe hBD).toEquiv
    rw [←hcard] at hpB
    exact hpB.trans (card_dvd_of_le (subgroupOf_mono D (show B≤K from le_sup_left)))
  have hPK:(derivedSylow:Subgroup D)≤K.subgroupOf D := by
    intro x hx
    have hm:x.val∈derivedSylowAmbient:= by
      rw [←derivedSylow_map_subtype]
      exact mem_map_of_mem DerivedModel.subtype hx
    exact (le_sup_right : S≤K) (hP hm)
  have htop:=SevenSylowOvergroups.eq_top_of_seven_dvd (K.subgroupOf D) hPK h7
  have hDK:D≤K := by
    intro x hx
    have hh:(⟨x,hx⟩:D)∈K.subgroupOf D := by rw [htop];exact mem_top _
    exact hh
  have h3:3∣Nat.card K := by
    apply dvd_trans _ (card_dvd_of_le hDK)
    rw [DerivedEvenOrder.card_derived_binary (by simp)];decide
  have hprod:=card_set_mul_mul_card_inf B S
  rw [←coe_sup_of_set_mul_comm B S hperm] at hprod
  have hd:3∣Nat.card B*Nat.card S := hprod ▸ (dvd_mul_of_dvd_left h3 _)
  rcases Nat.prime_three.dvd_mul.mp hd with hb|hs
  · obtain ⟨n,hn⟩:=hB.exists_card_eq
    rw [hn] at hb
    exact (by decide:¬3∣7) (Nat.prime_three.dvd_of_dvd_pow hb)
  · obtain ⟨n,hn⟩:=hS.exists_card_eq
    rw [hn] at hs
    exact (by decide:¬3∣2) (Nat.prime_three.dvd_of_dvd_pow hs)
end Atlas.G2.BinaryLargePrimeSylow
