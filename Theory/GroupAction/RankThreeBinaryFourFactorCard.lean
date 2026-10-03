module
public import Theory.GroupAction.RankThreeBinaryFixedFactorIndependence
/-!
# Four cubic factors for a faithful rank-three binary action

Let A be elementary binary of order eight, acting faithfully on elementary
cubic F. Suppose the whole fixed subgroup is trivial, each nonidentity
actor has fixed subgroup of order at most nine, and the number of nontrivial
index-two fixed factors is a power of two. Then F has order81. The explicit
power-of-two count is the input supplied by Sylow transitivity in the graph
application; it is not inferred without that argument.

The fixed factors have order three and are independent by the preceding
two modules. Coprime fixed-point generation makes their join all of F.
If there are n factors, faithfulness embeds A in the product of the n
order-two actor quotients, giving n≥3. Each factor has three nonidentity
actors fixing it, while any such actor fixes at most two factors: three
independent cubic factors would exceed its centralizer bound of nine.
Counting these incidences gives3n≤14, hence n≤4. The supplied power-of-two
condition forces n=4, and the product cardinality is3^4.

This is the final count after Stellmacher (8.6)(21), printed p.45. The
literal native actor, its faithfulness, whole-fixed-free property and Sylow
transitivity remain explicit obligations of the separate application.
-/

open scoped IsMulCommutative

private theorem card_nonidentity
    {A : Type*} [Group A] [Finite A] : Nat.card {a : A // a ≠ 1} = Nat.card A - 1 := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]

public theorem rank_three_binary_fixed_factor_card
    {A F : Type*} [Group A] [Finite A] [Group F] [Finite F]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 F]
    [MulDistribMulAction A F] [FaithfulSMul A F]
    (hA : Nat.card A = 8)
    (hfixed : ∀ a : A, a ≠ 1 →
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9)
    (hfull : FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥)
    (hcount : ∃ k : ℕ, Nat.card
      {K : Subgroup A // K.index = 2 ∧ FixedPoints.subgroup K F ≠ ⊥} = 2^k) :
    Nat.card F = 81 := by
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
  have hincidence (a : {a : A // a ≠ 1}) : Nat.card {i : I // a.val ∈ i.val} ≤ 2 := by
    let J := {i : I // a.val ∈ i.val}
    let _ : Fintype J := Fintype.ofFinite J
    have hsub : (⨆ j : J, H j.val) ≤ FixedPoints.subgroup (Subgroup.zpowers a.val) F := by
      refine iSup_le fun j x hx b => ?_
      exact hx ⟨b,(Subgroup.zpowers_le.mpr j.property) b.property⟩
    have hinds : iSupIndep (fun j : J => H j.val) := hind.comp Subtype.val_injective
    have hh := Subgroup.natCard_iSup_of_iSupIndep (fun j : J => H j.val)
      (fun _ _ _ _ _ _ _ => Commute.all _ _) hinds
    have hsmall := (Subgroup.card_le_of_le hsub).trans (hfixed a a.property)
    rw [hh] at hsmall
    simp only [hcard,Finset.prod_const,Finset.card_univ] at hsmall
    rw [Nat.card_eq_fintype_card]
    change Fintype.card J ≤ 2
    by_contra hlarge
    have h27 : 27 ≤ 3^(Fintype.card J) :=
      Nat.pow_le_pow_right (by decide : 0 < (3:ℕ)) (show 3 ≤ Fintype.card J by omega)
    omega
  have hKcard (i : I) : Nat.card i.val = 4 := by
    have hh := i.val.index_mul_card
    rw [i.property.1,hA] at hh
    omega
  have hrow (i : I) : Nat.card {a : A // a ∈ i.val ∧ a ≠ 1} = 3 := by
    let e : {a : A // a ∈ i.val ∧ a ≠ 1} ≃ {a : i.val // a ≠ 1} := {
      toFun := fun a => ⟨⟨a,a.property.1⟩,fun h => a.property.2 (congrArg Subtype.val h)⟩
      invFun := fun a => ⟨a.val,⟨a.val.property,fun h => a.property (Subtype.ext h)⟩⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
    rw [Nat.card_congr e,card_nonidentity,hKcard]
  have htotal : 3 * Nat.card I ≤ 14 := by
    let e : (Σ i : I, {a : A // a ∈ i.val ∧ a ≠ 1}) ≃
        (Σ a : {a : A // a ≠ 1}, {i : I // a.val ∈ i.val}) := {
      toFun := fun p => ⟨⟨p.2,p.2.property.2⟩,⟨p.1,p.2.property.1⟩⟩
      invFun := fun p => ⟨p.2,⟨p.1,⟨p.2.property,p.1.property⟩⟩⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro p; cases p; rfl }
    have he := Nat.card_congr e
    rw [Nat.card_sigma,Nat.card_sigma] at he
    simp only [hrow,Finset.sum_const,Finset.card_univ,smul_eq_mul] at he
    have hbound := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hincidence a)
    rw [←he] at hbound
    have hseven : Fintype.card {a : A // a ≠ 1} = 7 := by
      rw [←Nat.card_eq_fintype_card,card_nonidentity,hA]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hseven] at hbound
    rw [Nat.card_eq_fintype_card]
    omega
  let diagonal : A →* (∀ i : I, A ⧸ i.val) := {
    toFun := fun a i => QuotientGroup.mk' i.val a
    map_one' := by funext i; exact map_one _
    map_mul' := by intro a b; funext i; exact map_mul _ _ _ }
  have hdiag : Function.Injective diagonal := by
    rw [←MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro a ha
    have hmem (i : I) : a ∈ i.val := by
      apply (QuotientGroup.eq_one_iff (N := i.val) a).mp
      exact congrFun (MonoidHom.mem_ker.mp ha) i
    have hfix : (⨆ i, H i) ≤ FixedPoints.subgroup (Subgroup.zpowers a) F := by
      refine iSup_le fun i x hx b => ?_
      exact hx ⟨b,(Subgroup.zpowers_le.mpr (hmem i)) b.property⟩
    rw [hgen] at hfix
    change a = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
    intro x
    have hx := hfix (Subgroup.mem_top x) ⟨a,Subgroup.mem_zpowers a⟩
    simpa only [Subgroup.smul_def,one_smul] using hx
  have hlow : 8 ≤ 2^(Nat.card I) := by
    have hh := Nat.card_le_card_of_injective diagonal hdiag
    rw [hA,Nat.card_pi] at hh
    have hi (i : I) : Nat.card (A ⧸ i.val) = 2 := by rw [←Subgroup.index_eq_card,i.property.1]
    simpa only [hi,Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using hh
  have hnlow : 3 ≤ Nat.card I := by
    by_contra h
    have hpow : 2^(Nat.card I) ≤ 4 := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show Nat.card I ≤ 2 by omega)
    omega
  obtain ⟨k,hk⟩ := hcount
  change Nat.card I = 2^k at hk
  have hkle : k ≤ 2 := by
    by_contra h
    have hp : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 3 ≤ k by omega)
    omega
  have hI : Nat.card I = 4 := by
    interval_cases k
    · have hk0 : Nat.card I = 1 := hk
      omega
    · have hk1 : Nat.card I = 2 := hk
      omega
    · exact hk
  rw [hFcard,hI]
  decide
