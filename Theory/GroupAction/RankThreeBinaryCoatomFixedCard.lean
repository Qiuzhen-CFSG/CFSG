module
public import Theory.GroupAction.RankThreeBinaryElementaryFixed

/-!
# Order-three fixed subgroups for rank-three binary actors

Let an elementary binary group A of order eight act faithfully on a finite
three-group F. Suppose every nonidentity actor has fixed subgroup of order
at most nine. Then each nontrivial fixed subgroup for an index-two subgroup
of A has order three. Neither F elementary nor C_F(A)=1 is assumed.

Such a fixed subgroup has order one, three, or nine. If one has order nine,
its actor subgroup meets every cyclic-quotient actor subgroup nontrivially.
The fixed group of a nonidentity element in their intersection contains
the chosen order-nine subgroup and has order at most nine. Thus every
cyclic-quotient fixed subgroup lies in the chosen one. Coprime fixed-point
generation makes it all of F, contradicting faithful action because its
index-two actor subgroup has order four.

This supplies the |E_i|=3 part of Stellmacher (8.6)(21), printed p.45. The
actual graph application separately proves the order-eight actor and its
faithfulness on the residual image; the later direct-product count is not
assumed here.
-/

open scoped IsMulCommutative
private theorem cyclic_quotient_card_lower
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 8) (Y : Subgroup A)
    (hcyc : IsCyclic (A ⧸ Y)) : 4 ≤ Nat.card Y := by
  have hdiv : Nat.card (A ⧸ Y) ∣ 2 := by
    rw [←hcyc.exponent_eq_card]
    exact (Group.exponent_quotient_dvd Y).trans
      (IsElementaryAbelian.exponent_dvd_p 2 A)
  have hbound := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  have hproduct := Subgroup.card_eq_card_quotient_mul_card_subgroup Y
  rw [hcard] at hproduct
  nlinarith

private theorem cyclic_quotient_intersection_ne_bot
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 8) (K Y : Subgroup A)
    (hK : IsCyclic (A ⧸ K)) (hY : IsCyclic (A ⧸ Y)) : K ⊓ Y ≠ ⊥ := by
  have hKcard := cyclic_quotient_card_lower hcard K hK
  have hYcard := cyclic_quotient_card_lower hcard Y hY
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes K Y
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hsup : Nat.card (K ⊔ Y : Subgroup A) ≤ 8 := by
    simpa only [hcard] using Nat.card_le_card_of_injective
      (K ⊔ Y : Subgroup A).subtype (K ⊔ Y : Subgroup A).subtype_injective
  intro heq
  rw [heq,Subgroup.card_bot,one_mul] at hprod
  nlinarith

private theorem fixed_le_cyclic_fixed
    {A F : Type*} [Group A] [Group F] [MulDistribMulAction A F]
    (Y : Subgroup A) (a : A) (ha : a ∈ Y) :
    FixedPoints.subgroup Y F ≤ FixedPoints.subgroup (Subgroup.zpowers a) F := by
  intro x hx z
  exact hx ⟨z,(Subgroup.zpowers_le.mpr ha) z.property⟩

public theorem rank_three_binary_coatom_fixed_card
    {A F : Type*} [Group A] [Finite A] [Group F] [Finite F]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A F] [FaithfulSMul A F]
    (hA : Nat.card A = 8) (hF : IsPGroup 3 F)
    (hfixed : ∀ a : A, a ≠ 1 →
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9)
    (K : Subgroup A) (hK : K.index = 2)
    (hne : FixedPoints.subgroup K F ≠ ⊥) :
    Nat.card (FixedPoints.subgroup K F) = 3 := by
  classical
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let _ : Fact (IsPGroup 3 F) := ⟨hF⟩
  let C := FixedPoints.subgroup K F
  have hKcyc : IsCyclic (A ⧸ K) := isCyclic_of_prime_card (by
    rw [←Subgroup.index_eq_card,hK])
  have hKcard : Nat.card K = 4 := by
    have hh := K.card_mul_index
    rw [hK,hA] at hh
    omega
  have hCbound : Nat.card C ≤ 9 := by
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (cyclic_quotient_intersection_ne_bot hA K K hKcyc hKcyc)
    have hane : (a:A) ≠ 1 := fun h => ha (Subtype.ext h)
    exact (Subgroup.card_le_of_le (fixed_le_cyclic_fixed K a a.property.1)).trans
      (hfixed a hane)
  have hnotNine : Nat.card C ≠ 9 := by
    intro hCcard
    have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
      (G := F) (A := A) (q := 3) (show Nat.Coprime (Nat.card A) 3 by rw [hA]; decide)
    have hCtop : C = ⊤ := by
      apply top_unique
      rw [←hgen]
      refine iSup₂_le fun Y hY => ?_
      obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (cyclic_quotient_intersection_ne_bot hA K Y hKcyc hY)
      have hane : (a:A) ≠ 1 := fun h => ha (Subtype.ext h)
      have hsame : C = FixedPoints.subgroup (Subgroup.zpowers (a:A)) F :=
        Subgroup.eq_of_le_of_card_ge (fixed_le_cyclic_fixed K a a.property.1)
          (by rw [hCcard]; exact hfixed a hane)
      rw [hsame]
      exact fixed_le_cyclic_fixed Y a a.property.2
    have hKbot : K = ⊥ := by
      apply bot_unique
      intro a ha
      change a = 1
      apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
      intro x
      have hx : x ∈ C := hCtop.ge (Subgroup.mem_top x)
      simpa only [Subgroup.smul_def,one_smul] using hx ⟨a,ha⟩
    rw [hKbot,Subgroup.card_bot] at hKcard
    omega
  obtain ⟨n,hn⟩ := (hF.to_subgroup C).exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra h
    have hp : 27 ≤ 3^n := Nat.pow_le_pow_right (by decide : 0 < (3:ℕ)) (show 3 ≤ n by omega)
    rw [←hn] at hp
    omega
  interval_cases n
  · exact (hne (Subgroup.card_eq_one.mp hn)).elim
  · exact hn
  · exact (hnotNine hn).elim
