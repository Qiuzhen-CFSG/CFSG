module
public import Theory.GroupAction.RankThreeBinaryFourFactorCard
/-!
# Exactly four active cubic fixed factors

Retain the faithful elementary binary actor of order eight, its elementary
cubic module F, whole fixed-point freedom, nonidentity fixed-cardinality
bound of nine, and the derived two-power factor-count hypothesis of the
preceding cardinality theorem. The actual set of nontrivial coatom fixed
factors has cardinal four.

Every active factor has order three. Coprime fixed-point generation and
full independence identify |F| with three to the power of the number of
active factors. The existing order81 theorem and injectivity of natural
powers give the exact count. This leaves the original cardinality theorem
and all of its public hypotheses unchanged.

Source: Stellmacher (8.6)(21), printed p.45. This exposes the exact orbit
size needed by the native Sylow-order bounds in case C.
-/

open scoped IsMulCommutative
public theorem rank_three_binary_fixed_factor_count_eq_four
    {A F : Type*} [Group A] [Finite A] [Group F] [Finite F]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 F]
    [MulDistribMulAction A F] [FaithfulSMul A F]
    (hA : Nat.card A = 8)
    (hfixed : ∀ a : A, a ≠ 1 →
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9)
    (hfull : FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥)
    (hcount : ∃ k : ℕ, Nat.card
      {K : Subgroup A // K.index = 2 ∧ FixedPoints.subgroup K F ≠ ⊥} = 2^k) :
    Nat.card {K : Subgroup A // K.index = 2 ∧ FixedPoints.subgroup K F ≠ ⊥} = 4 := by
  classical
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let _ : CommGroup F := IsMulCommutative.instCommGroup
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype F := Fintype.ofFinite F
  let I := {K : Subgroup A // K.index = 2 ∧ FixedPoints.subgroup K F ≠ ⊥}
  let _ : Fintype I := Fintype.ofFinite I
  let H (i : I) := FixedPoints.subgroup i.val F
  have hF : IsPGroup 3 F := IsElementaryAbelian.isPGroup 3 F
  let _ : Fact (IsPGroup 3 F) := ⟨hF⟩
  have hcard (i : I) : Nat.card (H i) = 3 :=
    rank_three_binary_coatom_fixed_card hA hF hfixed i.val i.property.1 i.property.2
  have hind : iSupIndep H := by
    let inclusion : I → {K : Subgroup A // K.index = 2} := fun i => ⟨i.val,i.property.1⟩
    have hinj : Function.Injective inclusion := fun i j h => Subtype.ext (congrArg (fun k : {K : Subgroup A // K.index = 2} => k.val) h)
    exact (rank_three_binary_fixed_factors_independent hA hfull).comp hinj
  have hgen : (⨆ i, H i) = ⊤ := by
    have h := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
      (G := F) (A := A) (q := 3) (show Nat.Coprime (Nat.card A) 3 by rw [hA]; decide)
    apply top_unique
    rw [←h]
    refine iSup₂_le fun K hK => ?_
    have hdiv : K.index ∣ 2 := by
      rw [Subgroup.index_eq_card,←hK.exponent_eq_card]
      exact (Group.exponent_quotient_dvd K).trans (IsElementaryAbelian.exponent_dvd_p 2 A)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · rw [Subgroup.index_eq_one.mp hone,hfull]
      exact bot_le
    · by_cases hbot : FixedPoints.subgroup K F = ⊥
      · rw [hbot]; exact bot_le
      · exact le_iSup H (⟨K,htwo,hbot⟩:I)
  have hcomm : Pairwise fun i j : I => ∀ x y : F, x ∈ H i → y ∈ H j → Commute x y :=
    fun _ _ _ _ _ _ _ => Commute.all _ _
  have hFcard : Nat.card F = 3^(Nat.card I) := by
    have hh := Subgroup.natCard_iSup_of_iSupIndep H hcomm hind
    rw [hgen,Nat.card_congr Subgroup.topEquiv.toEquiv] at hh
    simpa only [hcard,Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using hh
  have h81 := rank_three_binary_fixed_factor_card hA hfixed hfull hcount
  apply Nat.pow_right_injective (by decide : 2 ≤ (3:ℕ))
  change 3^(Nat.card I) = 3^4
  rw [←hFcard,h81]
