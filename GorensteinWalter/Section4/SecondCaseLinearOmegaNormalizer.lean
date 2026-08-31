module

public import GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import FeitThompson.GroupAction.Cardinalities
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.Tactic

/-! # The normalizer of the fixed prime-order part inside omega

Shared infrastructure for the linear omega argument: the ambient copy `Q`
of the omega subgroup is a noncyclic `p`-group, the fixed part `P` lies in
`A`, the `s`-fixed elements of `Q` lie in `P`, and the normalizer of `P`
inside `Q` is exactly `A`.
-/

noncomputable section

namespace GorensteinWalter

open scoped Finset

universe u

/-- The ambient copy of `Q` has exponent `p`. -/
public theorem secondCase_linear_omega_QG_exponent
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    Monoid.exponent (od.Q.map c.U.subtype) = od.p := by
  let eQ : od.Q ≃* od.Q.map c.U.subtype :=
    Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
  exact (Monoid.exponent_eq_of_mulEquiv eQ).symm.trans od.Q_exponent

/-- The ambient copy of `Q` is a `p`-group. -/
public theorem secondCase_linear_omega_QG_isPGroup
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    IsPGroup od.p (od.Q.map c.U.subtype) := by
  intro x
  refine ⟨1, ?_⟩
  have hx : x ^ od.p = 1 :=
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (by rw [secondCase_linear_omega_QG_exponent c w d od]) x)
  simpa [pow_one] using hx

/-- The ambient copy of `Q` is not cyclic. -/
public theorem secondCase_linear_omega_QG_not_cyclic
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    ¬ IsCyclic (od.Q.map c.U.subtype) := by
  intro hcyc
  let eQ : od.Q ≃* od.Q.map c.U.subtype :=
    Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
  exact od.Q_not_cyclic (eQ.isCyclic.mpr hcyc)

/-- The ambient copy of `Q` is nontrivial (a noncyclic `p`-group). -/
public theorem secondCase_linear_omega_QG_nontrivial
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    Nontrivial (od.Q.map c.U.subtype) := by
  apply Finite.one_lt_card_iff_nontrivial.mp
  have hne : od.Q.map c.U.subtype ≠ ⊥ := by
    intro hbot
    apply secondCase_linear_omega_QG_not_cyclic c w d od
    rw [hbot]
    infer_instance
  have hpos : 0 < Nat.card (od.Q.map c.U.subtype) := Nat.card_pos
  have hne1 : Nat.card (od.Q.map c.U.subtype) ≠ 1 := by
    intro h1
    exact hne ((Subgroup.eq_bot_iff_card (H := od.Q.map c.U.subtype)).mpr h1)
  omega

/-- The fixed prime-order part `P` lies in `A`. -/
public theorem secondCase_linear_omega_P_le_A
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d) :
    od.P ≤ od.A := by
  rw [od.A_eq]
  exact le_sup_left

/-- Elements of `F(U)` of `p`-th power one are exactly the elements of `P`,
when `F` is the full `s`-fixed subgroup of `F(U)`. -/
public theorem secondCase_linear_omega_F_order_p_eq_P
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d)
    (hF_full : od.F = centralizerIn c.FU (od.s : G)) :
    {x : G | x ∈ od.F ∧ x ^ od.p = 1} = (od.P : Set G) := by
  classical
  let S : Set G := {x : G | x ∈ od.F ∧ x ^ od.p = 1}
  letI : Fintype (↥od.F) := Fintype.ofFinite (↥od.F)
  letI : IsCyclic (↥od.F) := od.F_cyclic
  have hp_pos : 0 < od.p := od.hp_prime.pos
  have hPsubS : (od.P : Set G) ⊆ S := by
    intro x hx
    exact ⟨od.P_le_F hx,
      (orderOf_dvd_iff_pow_eq_one (x := x) (n := od.p)).mp (by
        simpa [od.P_card] using (Subgroup.orderOf_dvd_natCard od.P hx))⟩
  have hScard : Nat.card {x : G // x ∈ S} = od.p := by
    apply le_antisymm
    · let e : {x : G // x ∈ S} ≃ {a : (↥od.F) // a ^ od.p = 1} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply Subtype.ext
            simpa using x.2.2⟩
          invFun := fun a => ⟨(a.1 : G), ⟨a.1.2, by
            exact congrArg Subtype.val a.2⟩⟩
          left_inv := by intro x; rfl
          right_inv := by intro a; rfl }
      calc
        Nat.card {x : G // x ∈ S} = Nat.card {a : (↥od.F) // a ^ od.p = 1} :=
          Nat.card_congr e
        _ = #{a : (↥od.F) | a ^ od.p = 1} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ od.p := IsCyclic.card_pow_eq_one_le (α := (↥od.F)) (n := od.p) hp_pos
    · have hle : Nat.card od.P ≤ Nat.card {x : G // x ∈ S} :=
        Nat.card_le_card_of_injective (fun x : od.P => ⟨(x : G), hPsubS x.2⟩) (by
          intro a b h
          simpa using congrArg Subtype.val h)
      rw [od.P_card] at hle
      exact hle
  have hcard : Nat.card {x : G // x ∈ S} ≤ Nat.card {x : G // x ∈ (od.P : Set G)} := by
    exact le_of_eq (by
      change Nat.card {x : G // x ∈ S} = Nat.card (↥od.P)
      rw [hScard, od.P_card])
  letI : Fintype (↥od.P) := Fintype.ofFinite (↥od.P)
  simpa [S] using (Set.eq_of_subset_of_card_le hPsubS (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard)).symm

/-- The `s`-fixed elements of `Q` lie in `P`. -/
public theorem secondCase_linear_omega_F_inter_QG_le_P
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d)
    (hF_full : od.F = centralizerIn c.FU (od.s : G)) :
    od.F ⊓ (od.Q.map c.U.subtype) ≤ od.P := by
  intro x hx
  have hxpow : x ^ od.p = 1 := by
    have hq : (⟨x, hx.2⟩ : od.Q.map c.U.subtype) ^ od.p = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one (G := od.Q.map c.U.subtype)
        (n := od.p)).mp (by rw [secondCase_linear_omega_QG_exponent c w d od]) ⟨x, hx.2⟩
    exact congrArg Subtype.val hq
  have hxS : x ∈ {x : G | x ∈ od.F ∧ x ^ od.p = 1} := ⟨hx.1, hxpow⟩
  rw [secondCase_linear_omega_F_order_p_eq_P c w d od hF_full] at hxS
  exact hxS

/-- `P ∩ Q = 1` whenever `P` is not contained in `Q`. -/
public theorem secondCase_linear_omega_P_inter_QG_eq_bot_of_not_le
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d)
    (hPnotleQ : ¬ od.P ≤ od.Q.map c.U.subtype) :
    od.P ⊓ (od.Q.map c.U.subtype) = ⊥ := by
  classical
  let I : Subgroup G := od.P ⊓ (od.Q.map c.U.subtype)
  have hIdiv : Nat.card I ∣ od.p := by
    rw [← od.P_card]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hIne : Nat.card I ≠ od.p := by
    intro hIp
    have hIeqP : I = od.P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hIp, od.P_card])
    apply hPnotleQ
    rw [← hIeqP]
    exact inf_le_right
  have hIcard : Nat.card I = 1 :=
    ((Nat.dvd_prime od.hp_prime).mp hIdiv).resolve_right hIne
  exact (Subgroup.eq_bot_iff_card (H := I)).mpr hIcard

/-- Inside `Q`, the normalizer of the fixed prime-order part `P` is exactly
`A`, whenever the elements of `Q` normalizing `P` lie in `A`. -/
public theorem secondCase_linear_omega_normalizer_P_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (od : SecondCaseLinearOmegaData c w d)
    (hnormalizer_le_A :
      (Subgroup.normalizer (od.P : Set G)) ⊓ (od.Q.map c.U.subtype) ≤ od.A)
    (hPleQ : od.P ≤ od.Q.map c.U.subtype) :
    (Subgroup.normalizer (od.P : Set G)) ⊓ (od.Q.map c.U.subtype) = od.A := by
  classical
  let QG : Subgroup G := od.Q.map c.U.subtype
  let FQ : Subgroup QG := od.P.subgroupOf QG
  have hFQcard : Nat.card FQ = od.p := by
    calc
      Nat.card FQ = Nat.card od.P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleQ).toEquiv
      _ = od.p := od.P_card
  letI : Fact (Nat.Prime od.p) := ⟨od.hp_prime⟩
  have hFQneTop : FQ ≠ ⊤ := by
    intro htop
    have hQGcard : Nat.card QG = od.p := by
      calc
        Nat.card QG = Nat.card (⊤ : Subgroup QG) := by simp
        _ = Nat.card FQ := by rw [← htop]
        _ = od.p := hFQcard
    exact secondCase_linear_omega_QG_not_cyclic c w d od
      (isCyclic_of_prime_card (p := od.p) hQGcard)
  have hQGp : IsPGroup od.p QG := secondCase_linear_omega_QG_isPGroup c w d od
  letI : Group.IsNilpotent QG := hQGp.isNilpotent
  have hlt : FQ < Subgroup.normalizer (FQ : Set QG) :=
    Group.normalizerCondition_of_isNilpotent FQ (lt_top_iff_ne_top.mpr hFQneTop)
  let NQ : Subgroup QG := Subgroup.normalizer (FQ : Set QG)
  let NG : Subgroup G := NQ.map QG.subtype
  have hNGleA : NG ≤ od.A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xQ, hxN, rfl⟩
    have hxNormP : (xQ : G) ∈ Subgroup.normalizer (od.P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        let yQ : QG := ⟨y, hPleQ hy⟩
        have hyFQ : yQ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
        have hconj := (Subgroup.mem_normalizer_iff.mp hxN yQ).mp hyFQ
        exact Subgroup.mem_subgroupOf.mp hconj
      · intro hy
        have hyQ : y ∈ QG := by
          have hconjQ : (xQ : G) * y * (xQ : G)⁻¹ ∈ QG := hPleQ hy
          have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem xQ.2) hconjQ) xQ.2
          simpa [mul_assoc] using hbackQ
        let yQ : QG := ⟨y, hyQ⟩
        have hconjFQ : xQ * yQ * xQ⁻¹ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.mp hxN yQ).mpr hconjFQ)
    exact hnormalizer_le_A ⟨hxNormP, xQ.2⟩
  have hNQcardGt : od.p < Nat.card NQ := by
    have hcardlt : Nat.card FQ < Nat.card NQ :=
      natCard_lt_of_subgroup_lt hlt
    rwa [hFQcard] at hcardlt
  have hNGcard : Nat.card NG = Nat.card NQ :=
    Subgroup.card_map_of_injective QG.subtype_injective
  have hNGdiv : Nat.card NG ∣ od.p ^ 2 := by
    rw [← od.A_card]
    exact Subgroup.card_dvd_of_le hNGleA
  have hNGcard_p2 : Nat.card NG = od.p ^ 2 := by
    have hgt : od.p < Nat.card NG := by rw [hNGcard]; exact hNQcardGt
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow od.hp_prime).mp hNGdiv
    rw [heq] at hgt
    have hp2 : 2 ≤ od.p := od.hp_prime.two_le
    have hk2 : k = 2 := by
      interval_cases k
      · exfalso
        have h : od.p < 1 := by simpa using hgt
        omega
      · exfalso
        have h : od.p < od.p := by simpa using hgt
        omega
      · rfl
    simpa [hk2] using heq
  have hNGeqA : NG = od.A :=
    Subgroup.eq_of_le_of_card_ge hNGleA (by rw [hNGcard_p2, od.A_card])
  have hNGeq : (Subgroup.normalizer (od.P : Set G)) ⊓ QG = NG := by
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro yQ
      constructor
      · intro hy
        have hyP : (yQ : G) ∈ od.P := Subgroup.mem_subgroupOf.mp hy
        have hconj := (Subgroup.mem_normalizer_iff.mp hx.1 (yQ : G)).mp hyP
        exact Subgroup.mem_subgroupOf.mpr hconj
      · intro hy
        exact Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp hx.1 (yQ : G)).mpr
            (Subgroup.mem_subgroupOf.mp hy))
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xQ, hxN, rfl⟩
      constructor
      · change (xQ : G) ∈ Subgroup.normalizer ((od.P : Set G))
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hyQ : y ∈ QG := hPleQ hy
          let yQ : QG := ⟨y, hyQ⟩
          have hyFQ : yQ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
          have hconj := (Subgroup.mem_normalizer_iff.mp hxN yQ).mp hyFQ
          exact Subgroup.mem_subgroupOf.mp hconj
        · intro hy
          have hyQ : y ∈ QG := by
            have hconjQ : (xQ : G) * y * (xQ : G)⁻¹ ∈ QG := hPleQ hy
            have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem xQ.2) hconjQ) xQ.2
            simpa [mul_assoc] using hbackQ
          let yQ : QG := ⟨y, hyQ⟩
          have hconjFQ : xQ * yQ * xQ⁻¹ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
          exact Subgroup.mem_subgroupOf.mp
            ((Subgroup.mem_normalizer_iff.mp hxN yQ).mpr hconjFQ)
      · exact xQ.2
  rw [hNGeq]
  exact hNGeqA

end GorensteinWalter
