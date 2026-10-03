module

public import Stellmacher.Recognition.LyonsU3Four.AutomizerBounds
public import Stellmacher.Recognition.LyonsU3Four.SquareRoots
public import Theory.GroupAction.Invariant
public import Theory.GroupAction.PrimeDegreeCoprimeIndex

/-!
# Excluding nine from the Lyons Sylow automizer

If nine divides the full automorphism-group order, its Sylow three-subgroups
have order nine by the bound 315. Such a subgroup A is abelian and remains
transitive on the three central involutions, since its index is prime to three.
The stabilizer B of one involution has order three and fixes the whole center.

Commutativity makes the B-fixed square-root fibers over the three involutions
equinumerous, of size r. The orbit congruence on a twenty-element root fiber
gives r ≡ 2 modulo three. Thus the B-fixed subgroup has order 4 + 3r, congruent
to one modulo nine. Its order divides 64 and it contains the center, so it is
all of S. Faithfulness of evaluation then contradicts the order of B.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
printed pp. 372–373. This counting argument takes place in the full
automorphism group and is independent of the exclusion of automizer order three.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- Nine does not divide the order of the full automorphism group of S. -/
public theorem not_nine_dvd_card_mulAut
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : ¬ 9 ∣ Nat.card (MulAut S) := by
  classical
  intro hd9
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let A : Sylow 3 (MulAut S) := default
  have hA9 : Nat.card A = 9 := by
    obtain ⟨n, hn⟩ := A.isPGroup'.exists_card_eq
    have hodd : Odd (Nat.card A) := hn ▸ (by norm_num : Odd 3).pow
    have hd315 := odd_dvd_mulAut_card_dvd_315 S h hodd A.1.card_subgroup_dvd_card
    have hd := A.pow_dvd_card_of_pow_dvd_card (n := 2) hd9
    have hnle : n ≤ 2 := by
      by_contra! hnlarge
      have hd27 : 27 ∣ 315 := (show 3 ^ 3 ∣ Nat.card A by
        rw [hn]
        exact pow_dvd_pow 3 hnlarge).trans hd315
      norm_num at hd27
    rw [hn] at hd
    interval_cases n <;> norm_num at hd
    exact hn
  let : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3) hA9
  -- Transfer transitivity from the full automorphism group to its Sylow subgroup.
  let Z := Subgroup.center S
  let : IsInvariant (MulAut S) S Z := isInvariant_of_characteristic Z
  let X := {z : Z // z ≠ 1}
  let : MulAction (MulAut S) X :=
    { smul a z := ⟨a • z.val, fun he => z.property ((MulAction.injective a)
          (he.trans (smul_one a).symm))⟩
      one_smul z := Subtype.ext (one_smul _ z.val)
      mul_smul a b z := Subtype.ext (mul_smul a b z.val) }
  have hX : Nat.card X = 3 := by
    change Nat.card ↥(({1} : Set Z)ᶜ) = 3
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]
    rw [show Nat.card Z = 4 from h.center_card]
  let : MulAction.IsPretransitive (MulAut S) X := ⟨by
    intro x y
    obtain ⟨a, ha⟩ := center_nonidentity_exists_mulAut S h x.val.property y.val.property
      (fun he => x.property (Subtype.ext he)) (fun he => y.property (Subtype.ext he))
    exact ⟨a, Subtype.ext (Subtype.ext ha)⟩⟩
  let : MulAction.IsPretransitive A X :=
    MulAction.isPretransitive_of_prime_card_of_coprime_index (by decide) hX A.1
      ((Nat.prime_three.coprime_iff_not_dvd).mpr A.not_dvd_index)
  have : Nonempty X := (Nat.card_pos_iff.mp (show 0 < Nat.card X by omega)).1
  let z : X := Classical.choice this
  -- In the abelian transitive action, a point stabilizer fixes every point.
  let B : Subgroup A := MulAction.stabilizer A z
  have hB : Nat.card B = 3 := by
    have hi : B.index = 3 := (MulAction.index_stabilizer_of_transitive A z).trans hX
    have hc := B.card_mul_index
    rw [hi, hA9] at hc
    omega
  have hcomm (a b : A) (s : S) : a • (b • s) = b • (a • s) := by
    rw [← mul_smul, ← mul_smul, mul_comm']
  have hzfix (b : B) (w : Z) : b • (w : S) = w := by
    by_cases hw : w = 1
    · subst w
      exact smul_one b
    · obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A z (⟨w, hw⟩ : X)
      have ha' : a • (z.val : S) = w := congrArg (fun x : X => (x.val : S)) ha
      have hb : (b : A) • (z.val : S) = z.val :=
        congrArg (fun x : X => (x.val : S)) b.property
      change (b : A) • (w : S) = w
      rw [← ha', ← hcomm, hb]
  -- Every element of A preserves the B-fixed subgroup.
  let F := FixedPoints.subgroup B S
  have hpreserve (a : A) {s : S} (hs : s ∈ F) : a • s ∈ F := by
    intro b
    change (b : A) • (a • s) = a • s
    rw [← hcomm]
    exact congrArg (fun t : S => a • t) (hs b)
  let fa (a : A) : F ≃ F :=
    { toFun s := ⟨a • (s : S), hpreserve a s.property⟩
      invFun s := ⟨a⁻¹ • (s : S), hpreserve a⁻¹ s.property⟩
      left_inv s := Subtype.ext (inv_smul_smul a (s : S))
      right_inv s := Subtype.ext (smul_inv_smul a (s : S)) }
  let R := {s : S // s ^ 2 = (z.val : S)}
  let : MulAction B R :=
    { smul b s := ⟨b • (s : S), by
        change (((b : A) : MulAut S) (s : S)) ^ 2 = (z.val : S)
        rw [← map_pow, s.property]
        exact hzfix b z.val⟩
      one_smul s := Subtype.ext (one_smul B (s : S))
      mul_smul b c s := Subtype.ext (mul_smul b c (s : S)) }
  let r := Nat.card {s : F // (s.val : S) ^ 2 = (z.val : S)}
  have hr : r % 3 = 2 := by
    have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
    have hm := hp.card_modEq_card_fixedPoints R
    have he : MulAction.fixedPoints B R ≃ {s : F // (s.val : S) ^ 2 = (z.val : S)} :=
      { toFun s := ⟨⟨s.val.val, fun b => congrArg Subtype.val (s.property b)⟩, s.val.property⟩
        invFun s := ⟨⟨s.val.val, s.property⟩, fun b => Subtype.ext (s.val.property b)⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    have hR : Nat.card R = 20 := square_roots_card S h z.val.property
      (fun he => z.property (Subtype.ext he))
    change Nat.card R % 3 = Nat.card (MulAction.fixedPoints B R) % 3 at hm
    rw [hR, Nat.card_congr he] at hm
    exact hm.symm
  -- Count the fixed subgroup by its squaring fibers over the center.
  have hFcount : Nat.card F = 4 + 3 * r := by
    let _ := Fintype.ofFinite Z
    let q : F → Z := fun s => ⟨(s : S) ^ 2, square_mem_center S h s⟩
    have hf (w : Z) : Nat.card {s : F // q s = w} =
        Nat.card {s : F // (s : S) ^ 2 = (w : S)} := by
      apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl F) _)
      intro s
      exact Subtype.ext_iff
    have hs : Nat.card F = ∑ w : Z, Nat.card {s : F // (s : S) ^ 2 = (w : S)} := by
      calc
        Nat.card F = Nat.card ((w : Z) × {s : F // q s = w}) :=
          (Nat.card_congr (Equiv.sigmaFiberEquiv q)).symm
        _ = _ := by
          rw [Nat.card_sigma]
          exact Finset.sum_congr rfl (fun w _ => hf w)
    have he (w : Z) : Nat.card {s : F // (s : S) ^ 2 = (w : S)} =
        if w = 1 then 4 else r := by
      split_ifs with hw
      · subst w
        let e : {s : F // (s : S) ^ 2 = 1} ≃ Z :=
          { toFun s := ⟨s.val.val, square_one_mem_center S h s.property⟩
            invFun w := ⟨⟨w, fun b => hzfix b w⟩, by
              let _ := h.center_elementary
              exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : S) w.property⟩
            left_inv _ := rfl
            right_inv _ := rfl }
        exact (Nat.card_congr e).trans h.center_card
      · obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A (⟨w, hw⟩ : X) z
        have ha' : ((a : MulAut S) (w : S)) = (z.val : S) :=
          congrArg (fun x : X => (x.val : S)) ha
        apply Nat.card_congr (Equiv.subtypeEquiv (fa a) _)
        intro s
        change (s : S) ^ 2 = (w : S) ↔ ((a : MulAut S) (s : S)) ^ 2 = (z.val : S)
        rw [← map_pow, ← ha']
        exact (a : MulAut S).injective.eq_iff.symm
    simp_rw [he] at hs
    have hc : Fintype.card Z = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact h.center_card
    simp only [Finset.sum_ite, Finset.filter_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_singleton, nsmul_eq_mul,
      Finset.filter_ne', Finset.card_erase_of_mem, Finset.card_univ, hc] at hs
    simpa using hs
  have hdvd : Nat.card F ∣ 2 ^ 6 := by
    change Nat.card F ∣ 64
    rw [← h.card]
    exact F.card_subgroup_dvd_card
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hF : Nat.card F = 64 := by
    interval_cases n <;> norm_num only [Nat.reducePow] at he <;> omega
  have htop : F = ⊤ := F.eq_top_of_card_eq (hF.trans h.card.symm)
  have hBbot : B = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall B).mpr
    intro b hb
    apply Subtype.ext
    apply MulEquiv.ext
    intro s
    have hs : s ∈ F := by rw [htop]; trivial
    exact hs ⟨b, hb⟩
  rw [hBbot, Subgroup.card_bot] at hB
  omega

/-- In particular, the actual Sylow automizer has no factor nine. -/
public theorem not_nine_dvd_automizerIndex
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : ¬ 9 ∣ automizerIndex S := by
  intro hd
  exact not_nine_dvd_card_mulAut S h (hd.trans (automizerIndex_dvd_card_mulAut S))

end Stellmacher.Recognition.LyonsU3Four
