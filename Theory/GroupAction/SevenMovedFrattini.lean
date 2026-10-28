module
public import Theory.GroupAction.CoprimeMovingQuotient
public import Theory.Frattini.PGroupMap
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# The Frattini quotient of a fully moved seven-action

For a coprime action on a finite p-group P with [P,A] = P, the action
on P/Φ(P) has no nonidentity common fixed points. This follows by mapping
the commutator onto the elementary Frattini quotient and using its coprime
fixed/moving decomposition. Consequently C_P(A) lies in Φ(P).

When |A| = 7 and P is a nontrivial two-group, the quotient action is
faithful and |P/Φ(P)| is a positive power of eight: orbit counting gives
2^d = 1 modulo seven, hence 3 divides d.

Source: standard coprime action and Burnside basis theory. The literal
seven-moved core application in Aschbacher--Smith 5.1.13 (pp.635--638)
is in RankOneModuleGenericExceptionalCartanLocalBinarySevenFrattini.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
variable {P A : Type*} [Group P] [Finite P] [Group A] [Finite A]
  [MulDistribMulAction A P]

/-- A fully moved coprime action has no fixed points on the Frattini quotient. -/
theorem fixedPoints_frattini_eq_bot_of_coprime_moved {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hc : Nat.Coprime (Nat.card A) (Nat.card P))
    (hm : commutatorAction A P = ⊤) :
    letI : MulDistribMulAction A (P ⧸ frattini P) :=
      quotientMulDistribMulAction (frattini P) (isInvariant_of_characteristic _)
    FixedPoints.subgroup A (P ⧸ frattini P) = ⊥ := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsInvariant A P (frattini P) := isInvariant_of_characteristic _
  let : MulDistribMulAction A (P ⧸ frattini P) :=
    quotientMulDistribMulAction (frattini P) inferInstance
  let q := QuotientGroup.mk' (frattini P)
  have hq : (commutatorAction A P).map q = commutatorAction A (P ⧸ frattini P) :=
    commutatorAction_map_surjective q (QuotientGroup.mk'_surjective _) (fun _ _ => rfl)
  have hfull : commutatorAction A (P ⧸ frattini P) = ⊤ := by
    rw [←hq,hm,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hcop := hc.of_dvd_right (card_quotient_dvd_card (frattini P))
  have hd := (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (A := A) (G := P ⧸ frattini P) inferInstance hcop inferInstance).disjoint
  rw [hfull,disjoint_top] at hd
  exact hd

omit [Finite A] in
private theorem seven_size (hP : IsPGroup 2 P) (hA : Nat.card A = 7)
    (hf : FixedPoints.subgroup A P = ⊥) (hP0 : 1 < Nat.card P) :
    ∃ k : ℕ, 0 < k ∧ Nat.card P = 8^k := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have ha : IsPGroup 7 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  obtain ⟨k,hk⟩ := hP.exists_card_eq
  have hmod := ha.card_modEq_card_fixedPoints P
  change Nat.card P % 7 = Nat.card (FixedPoints.subgroup A P) % 7 at hmod
  rw [hf,card_bot,hk] at hmod
  have hr : k % 3 < 3 := Nat.mod_lt _ (by decide)
  have he : 2^k % 7 = 2^(k%3) % 7 := by
    conv_lhs => rw [←Nat.mod_add_div k 3,pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  rw [he] at hmod
  have hz : k%3 = 0 := by
    rcases (show k%3=0 ∨ k%3=1 ∨ k%3=2 by omega) with hh | hh | hh
    · exact hh
    · norm_num [hh] at hmod
    · norm_num [hh] at hmod
  refine ⟨k/3,?_,?_⟩
  · have hp : 0 < k := by
      by_contra hn
      have hzero : k=0 := by omega
      rw [hk,hzero] at hP0
      norm_num at hP0
    omega
  · rw [hk,←Nat.mod_add_div k 3,hz,zero_add,pow_mul]
    simp

/-- A fully moved nontrivial two-group has a faithful seven-action on its
Frattini quotient, of order a positive power of eight. -/
theorem seven_moved_frattini (hP : IsPGroup 2 P) (hA : Nat.card A = 7)
    (hm : commutatorAction A P = ⊤) (hP0 : 1 < Nat.card P) :
    let a := MulDistribMulAction.toMulAut A P
    let d := (quotientAut (frattini P)).comp a
    (∀ v : P ⧸ frattini P, (∀ b : A, d b v = v) → v = 1) ∧
      Function.Injective d ∧
      (∃ k : ℕ, 0 < k ∧ Nat.card (P ⧸ frattini P) = 8^k) ∧
      FixedPoints.subgroup A P ≤ frattini P := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsInvariant A P (frattini P) := isInvariant_of_characteristic _
  let : MulDistribMulAction A (P ⧸ frattini P) :=
    quotientMulDistribMulAction (frattini P) inferInstance
  have hc : Nat.Coprime (Nat.card A) (Nat.card P) := by
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hA,hk]
    exact (by decide : Nat.Coprime 7 2).pow_right k
  have hf := fixedPoints_frattini_eq_bot_of_coprime_moved hP hc hm
  have hq0 : 1 < Nat.card (P ⧸ frattini P) := by
    have hne : frattini P ≠ ⊤ := by
      intro ht
      have hz : (⊥ : Subgroup P) = ⊤ := frattini_nongenerating (by simpa using ht)
      have hh := congrArg (fun S : Subgroup P => Nat.card S) hz
      simp only [card_bot,card_top] at hh
      omega
    exact (frattini P).one_lt_index_of_ne_top hne
  let a := MulDistribMulAction.toMulAut A P
  let d := (quotientAut (frattini P)).comp a
  have he (b : A) (v : P ⧸ frattini P) : d b v = b • v := by
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (frattini P) v
    exact quotientAut_apply_mk _ _ _
  have hfixed (v : P ⧸ frattini P) (hv : ∀ b : A, d b v = v) : v=1 := by
    have hvf : v ∈ FixedPoints.subgroup A (P ⧸ frattini P) := by
      intro b
      rw [←he]
      exact hv b
    exact mem_bot.mp (hf ▸ hvf)
  have hinj : Function.Injective d := by
    let : Fact (Nat.card A).Prime := ⟨by rw [hA]; decide⟩
    apply (MonoidHom.ker_eq_bot_iff d).mp
    rcases d.ker.eq_bot_or_eq_top_of_prime_card with hb | ht
    · exact hb
    · have hall (v : P ⧸ frattini P) : v=1 := hfixed v (fun b => by
        have hb : d b=1 := ht.ge (mem_top b)
        rw [hb]; rfl)
      have hs : Subsingleton (P ⧸ frattini P) := ⟨fun v w => (hall v).trans (hall w).symm⟩
      have hn := Finite.card_le_one_iff_subsingleton.mpr hs
      omega
  refine ⟨hfixed,hinj,seven_size (hP.of_surjective _ (QuotientGroup.mk'_surjective _)) hA hf hq0,?_⟩
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hfixed
  intro b
  rw [he]
  change QuotientGroup.mk' (frattini P) (b • x) = QuotientGroup.mk' (frattini P) x
  rw [hx b]
end Theory.GroupAction


namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The ambient seven-moved subgroup retains its own faithful Frattini
action, and meets any subgroup fixed by the actor only inside its Frattini
subgroup. This statement retains the original ambient inclusions. -/
theorem seven_moved_subgroup_frattini (N B U : Subgroup G)
    (hN : IsPGroup 2 N) (hBN : B ≤ normalizer (N : Set G))
    (hb : Nat.card B = 7) (hP0 : ⁅N,B⁆ ≠ ⊥)
    (hBU : B ≤ centralizer (U : Set G)) :
    let P := ⁅N,B⁆
    ⁅P,B⁆ = P ∧
      P ⊓ U ≤ (frattini P).map P.subtype ∧
      (frattini P).map P.subtype ≤ (frattini N).map N.subtype ∧
      ∃ a : B →* MulAut P,
        (∀ (b : B) (v : P), ((a b v : P) : G) =
          (b : G) * (v : G) * (b : G)⁻¹) ∧
        let d := (quotientAut (frattini P)).comp a
        (∀ v : P ⧸ frattini P, (∀ b : B, d b v = v) → v = 1) ∧
        Function.Injective d ∧
        ∃ k : ℕ, 0 < k ∧ Nat.card (P ⧸ frattini P) = 8^k := by
  let P := ⁅N,B⁆
  have hPN : P ≤ N := le_normalizer_iff_commutator_le_left.mp hBN
  have hP : IsPGroup 2 P := hN.to_le hPN
  have hcop : Nat.Coprime (Nat.card B) (Nat.card N) := by
    obtain ⟨k,hk⟩ := hN.exists_card_eq
    rw [hb,hk]
    exact (by decide : Nat.Coprime 7 2).pow_right k
  have hid : ⁅P,B⁆ = P := by
    have hh := commutator_closure_coprime_idempotent N (B : Set G)
      (by simpa using hBN) (fun b hbB =>
        (hcop.of_dvd_left (by simpa only [Subgroup.orderOf_mk] using
          (_root_.orderOf_dvd_natCard (⟨b,hbB⟩ : B)))))
    simpa only [Subgroup.closure_eq] using hh
  have hBP : B ≤ normalizer (P : Set G) := normalizer_commutator_ge_right N B
  let : Normalizes B P := ⟨hBP⟩
  have hfull : commutatorAction B P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [commutatorAction_subgroup_conj_map_eq_commutator P B hBP,hid,
      ←MonoidHom.range_eq_map,range_subtype]
  have hcardP : 1 < Nat.card P := by
    apply Finite.one_lt_card_iff_nontrivial.mpr
    exact (nontrivial_iff_ne_bot P).mpr hP0
  obtain ⟨hfixed,hinj,hcard,hfixphi⟩ := Theory.GroupAction.seven_moved_frattini hP hb hfull hcardP
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Fact (IsPGroup 2 N) := ⟨hN⟩
  have hphi : (frattini P).map P.subtype ≤ (frattini N).map N.subtype := by
    have hh := map_mono (f := N.subtype) (frattini_map_le_of_isPGroup (p := 2) (inclusion hPN))
    rw [map_map] at hh
    exact hh
  refine ⟨hid,?_,hphi,MulDistribMulAction.toMulAut B P,fun _ _ => rfl,hfixed,hinj,hcard⟩
  intro x hx
  refine ⟨⟨x,hx.1⟩,hfixphi ?_,rfl⟩
  intro b
  apply Subtype.ext
  change (b : G)*x*(b : G)⁻¹=x
  have hh := hBU b.property x hx.2
  exact mul_inv_eq_of_eq_mul hh.symm
end Subgroup
