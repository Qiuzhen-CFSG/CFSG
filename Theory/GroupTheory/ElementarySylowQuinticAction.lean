module
public import Theory.GroupTheory.ElementarySylowResidualAction
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupAction.QuinticFixedIndex
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Quintic displacement in an inner Sylow action

A nontrivial two-group fully moved by a five-group has order at least
sixteen, by orbit counting on a nontrivial order-five image. For a
centerless group with two-group outer automorphisms, every quintic actor
is inner. Its elementary displacement is therefore an actual elementary
subgroup of the group. Normalization by the specified inner Sylow puts
that subgroup in the same Sylow, preserving relative normality. The
quintic subgroup is retained along with its literal displacement identity.
Coprime splitting forces a nonzero displacement of order at most 64 to
have order sixteen, and its normalizer has order divisible by five.

Source application: the original prime actor in Aschbacher--Smith
15.1.21--22, printed pp.1098--1100, refs/quasithin.pdf. The proof uses
only these elementary action hypotheses, before exchanged selection.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {K : Type*} [Group K] [Finite K]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A nontrivial two-group fully moved by a five-group has order at least sixteen. -/
theorem sixteen_le_card_of_quintic_movement {D : Type*} [Group D] [Finite D]
    (A B : Subgroup D) (hA : IsPGroup 2 A) (hB : IsPGroup 5 B)
    (hmove : ⁅A,B⁆ = A) (hne : A ≠ ⊥) : 16 ≤ Nat.card A := by
  have hn : B ≤ normalizer (A : Set D) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.le
  let f := A.normalizerMonoidHom.comp (inclusion hn)
  have hf : f.range ≠ ⊥ := by
    intro hh
    have hc : B ≤ centralizer (A : Set D) := by
      intro b hb
      have he : f ⟨b,hb⟩ = 1 := mem_bot.mp (hh ▸ (show f ⟨b,hb⟩ ∈ f.range from ⟨⟨b,hb⟩,rfl⟩))
      have hk : inclusion hn ⟨b,hb⟩ ∈ A.normalizerMonoidHom.ker := he
      rw [normalizerMonoidHom_ker] at hk
      exact hk
    apply hne
    rw [←hmove,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hp : IsPGroup 5 f.range := hB.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h5 : 5 ∣ Nat.card f.range := hp.card_eq_or_dvd.resolve_left (by
    intro he
    exact hf (card_eq_one.mp he))
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := f.range) 5 h5
  let C := zpowers a
  have hC : Nat.card C = 5 := (Nat.card_zpowers a).trans ha
  have hnot : FixedPoints.subgroup C A ≠ ⊤ := by
    intro ht
    have he : a = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      have hx : x ∈ FixedPoints.subgroup C A := ht ▸ mem_top x
      exact hx ⟨a,mem_zpowers a⟩
    simp [he] at ha
  exact Theory.GroupAction.sixteen_le_card_of_five_action_nontrivial hC hA hnot

/-- Quintic displacement is an actual large elementary subgroup normalized by the specified Sylow. -/
theorem exists_normal_elementary_pair_of_quintic_movement
    (hz : center K = ⊥) (ho : IsPGroup 2 (MulAut.Outer K))
    (P : Sylow 2 K) (A B : Subgroup (MulAut K)) [IsElementaryAbelian 2 A]
    (hB : IsPGroup 5 B)
    (hPA : (P : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤ normalizer (A : Set (MulAut K)))
    (hmove : ⁅A,B⁆ = A) (hne : A ≠ ⊥) :
    ∃ E D : Subgroup K, IsElementaryAbelian 2 E ∧ E ≤ (P : Subgroup K) ∧
      (P : Subgroup K) ≤ normalizer (E : Set K) ∧ IsPGroup 5 D ∧
      ⁅E,D⁆ = E ∧ E ≠ ⊥ ∧ 16 ≤ Nat.card E := by
  let c : K →* MulAut K := MulAut.conj
  have hci : Function.Injective c := conj_injective_of_center_eq_bot hz
  have hBI : B ≤ MulAut.innerSubgroup K := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup K)
    intro b hb
    apply (QuotientGroup.eq_one_iff _).mp
    obtain ⟨i,hi⟩ := hB ⟨b,hb⟩
    obtain ⟨j,hj⟩ := ho (q b)
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 5 2).pow i j)
    · apply orderOf_dvd_of_pow_eq_one
      change (q b) ^ (5 ^ i) = 1
      rw [←map_pow,show b ^ 5 ^ i = 1 from congrArg Subtype.val hi,map_one]
    · exact orderOf_dvd_of_pow_eq_one hj
  have hAI : A ≤ c.range := by
    rw [←hmove]
    exact (commutator_mono le_rfl hBI).trans (commutator_le_right _ _)
  let E := A.comap c
  have hEA : E.map c = A := map_comap_eq_self hAI
  let f : E →* A := c.restrict (fun x hx => hx)
  have hfi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (hci (congrArg Subtype.val he))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective f hfi
  have hPE : (P : Subgroup K) ≤ normalizer (E : Set K) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    change c y ∈ A ↔ c (x*y*x⁻¹) ∈ A
    rw [map_mul,map_mul,map_inv]
    exact (hPA (mem_map_of_mem c hx)) (c y)
  have hEP : E ≤ (P : Subgroup K) := by
    have hh := P.is_maximal' (P.isPGroup'.to_sup_of_normal_right'
      (IsElementaryAbelian.isPGroup 2 E) hPE) le_sup_left
    exact sup_eq_left.mp hh
  let D := B.comap c
  have hDB : D.map c = B := map_comap_eq_self hBI
  let fD : D →* B := c.restrict (fun x hx => hx)
  have hDi : Function.Injective fD := by
    intro x y he
    exact Subtype.ext (hci (congrArg Subtype.val he))
  have hD : IsPGroup 5 D := hB.of_injective fD hDi
  have hED : ⁅E,D⁆ = E := by
    apply map_injective hci
    rw [map_commutator,hEA,hDB,hmove]
  have hEn : E ≠ ⊥ := by
    intro hh
    apply hne
    rw [←hEA,hh,Subgroup.map_bot]
  refine ⟨E,D,inferInstance,hEP,hPE,hD,hED,hEn,?_⟩
  have hc := sixteen_le_card_of_quintic_movement A B
    (IsElementaryAbelian.isPGroup 2 A) hB hmove hne
  rwa [←hEA,card_map_of_injective hci] at hc

/-- Quintic displacement is an actual large elementary subgroup normalized by the specified Sylow. -/
theorem exists_normal_elementary_of_quintic_movement
    (hz : center K = ⊥) (ho : IsPGroup 2 (MulAut.Outer K))
    (P : Sylow 2 K) (A B : Subgroup (MulAut K)) [IsElementaryAbelian 2 A]
    (hB : IsPGroup 5 B)
    (hPA : (P : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤ normalizer (A : Set (MulAut K)))
    (hmove : ⁅A,B⁆ = A) (hne : A ≠ ⊥) :
    ∃ E : Subgroup K, IsElementaryAbelian 2 E ∧ E ≤ (P : Subgroup K) ∧
      (P : Subgroup K) ≤ normalizer (E : Set K) ∧ 16 ≤ Nat.card E := by
  obtain ⟨E,D,hE,hEP,hPE,_,_,_,hc⟩ :=
    exists_normal_elementary_pair_of_quintic_movement hz ho P A B hB hPA hmove hne
  exact ⟨E,hE,hEP,hPE,hc⟩

/-- At order at most 64, a nontrivial elementary quintic displacement has order sixteen. -/
theorem card_eq_sixteen_of_quintic_movement
    (E D : Subgroup K) [IsElementaryAbelian 2 E]
    (hD : IsPGroup 5 D) (hmove : ⁅E,D⁆ = E) (hne : E ≠ ⊥)
    (hc : Nat.card E ≤ 64) : Nat.card E = 16 := by
  let hE := IsElementaryAbelian.isPGroup 2 E
  have hn : D ≤ normalizer (E : Set K) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.le
  let _ : Normalizes D E := ⟨hn⟩
  have hm : commutatorAction D E = ⊤ := by
    apply map_injective E.subtype_injective
    rw [commutatorAction_subgroup_conj_map_eq_commutator E D hn,hmove,← MonoidHom.range_eq_map,range_subtype]
  have hcop : Nat.Coprime (Nat.card D) (Nat.card E) := by
    obtain ⟨i,hi⟩ := hD.exists_card_eq
    obtain ⟨j,hj⟩ := hE.exists_card_eq
    rw [hi,hj]
    exact (by decide : Nat.Coprime 5 2).pow i j
  have hd := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := E) (A := D)
    (Group.isSolvable_of_comm (fun x y : E => IsMulCommutative.is_comm.comm x y))
    hcop inferInstance
  have hfix : FixedPoints.subgroup D E = ⊥ := by
    have hh := hd.inf_eq_bot
    rwa [hm,inf_top_eq] at hh
  have hbound := FixedPoints.quintic_index_le_sixteen hD hE hc
  rw [hfix,index_bot] at hbound
  exact Nat.le_antisymm hbound
    (sixteen_le_card_of_quintic_movement E D hE hD hmove hne)

omit [Finite K] in
/-- A nontrivial quintic displacement has a normalizer whose order is divisible by five. -/
theorem five_dvd_normalizer_of_quintic_movement (E D : Subgroup K)
    (hD : IsPGroup 5 D) (hmove : ⁅E,D⁆ = E) (hne : E ≠ ⊥) :
    5 ∣ Nat.card (normalizer (E : Set K)) := by
  have hn : D ≤ normalizer (E : Set K) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.le
  have hDn : D ≠ ⊥ := by
    intro hh
    apply hne
    rw [←hmove,hh,commutator_bot_right]
  exact (hD.card_eq_or_dvd.resolve_left (fun he => hDn (card_eq_one.mp he))).trans
    (card_dvd_of_le hn)

end Theory.GroupTheory
