module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Quotients
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The two local products in the five-point tensor actors

A Sylow subgroup of a direct product is the product of its projections.
Its right projection normalizes the marked Borel. In the alternating case
self-normalization gives the local product C₂ × A₄. In the symmetric case,
the orders 12 and 8 generate the whole normalizer S₄, while the first
three-core together with the left Sylow generates S₃.

Source application: Aschbacher–Smith, Lemma 14.4.10(5), printed p.1011.
These are local product calculations; the original Borel's coordinates
are supplied by `ModelMarks` under the original quotient map.
-/

public section

open Subgroup
open Theory.SpecificGroups.TensorThreeFive
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements

private theorem prod_sup_prod {A D : Type*} [Group A] [Group D]
    (B C : Subgroup A) (E F : Subgroup D) :
    B.prod E ⊔ C.prod F = (B ⊔ C).prod (E ⊔ F) := by
  apply le_antisymm
    (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right))
  rw [prod_le_iff, Subgroup.map_sup, Subgroup.map_sup]
  have h₁ := prod_le_iff.mp (show B.prod E ≤ B.prod E ⊔ C.prod F from le_sup_left)
  have h₂ := prod_le_iff.mp (show C.prod F ≤ B.prod E ⊔ C.prod F from le_sup_right)
  exact ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩

private theorem sylow_prod {A D : Type*} [Group A] [Group D] [Finite A] [Finite D]
    (P : Sylow 2 (A × D)) :
    (P : Subgroup (A × D)) =
      (P.map (MonoidHom.fst A D)).prod (P.map (MonoidHom.snd A D)) := by
  apply Eq.symm
  apply P.is_maximal'
  · obtain ⟨m, hm⟩ := (P.isPGroup'.map (MonoidHom.fst A D)).exists_card_eq
    obtain ⟨n, hn⟩ := (P.isPGroup'.map (MonoidHom.snd A D)).exists_card_eq
    apply IsPGroup.of_card (n := m + n)
    rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, hm, hn, pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩

private theorem left_sylow_card {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 (S3 × D)) : Nat.card ↥(P.map (MonoidHom.fst S3 D)) = 2 := by
  let Q := P.mapSurjective (f := MonoidHom.fst S3 D) (fun x => ⟨(x,1),rfl⟩)
  have h := Q.card_eq_multiplicity
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial,
    show (6 : ℕ).factorization 2 = 1 from by
      rw [show 6 = 2 ^ 1 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
        Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)],
    show (120 : ℕ).factorization 2 = 3 from by
      rw [show 120 = 2 ^ 3 * 15 from rfl, Nat.factorization_mul (by decide) (by decide),
        Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]] at h
  exact h

/-- A₄ has no nontrivial two-group quotient. -/
theorem a4_twoPerfect : IsPPerfect 2 A4 := by
  change IsPPerfect 2 (alternatingGroup (Fin 4))
  rw [← Equiv.Perm.twoResidual_eq_alternating (Fin 4)]
  exact isPPerfect_pResidual 2

/-- Taking O² preserves any actual A₄ subgroup. -/
theorem twoResidual_eq_of_equiv_a4 {A : Type*} [Group A] (B : Subgroup A)
    (e : B ≃* A4) : twoResidual B = B := by
  have hp : IsPPerfect 2 B := a4_twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective
  rw [twoResidual, (pResidual_eq_top_iff 2 B).mpr hp,
    ← MonoidHom.range_eq_map, range_subtype]

private theorem rightProjection_le_normalizer {A D : Type*} [Group A] [Group D]
    (P : Subgroup (A × D)) (B : Subgroup D)
    (hn : P ≤ normalizer ((⊥ : Subgroup A).prod B : Set (A × D))) :
    P.map (MonoidHom.snd A D) ≤ normalizer (B : Set D) := by
  rintro x ⟨y, hy, rfl⟩ z
  have h := hn hy (1,z)
  change ((1 : A) = 1 ∧ z ∈ B) ↔ (y.1 * 1 * y.1⁻¹ = 1 ∧ y.2 * z * y.2⁻¹ ∈ B) at h
  change z ∈ B ↔ y.2 * z * y.2⁻¹ ∈ B
  simpa only [mul_one, mul_inv_cancel, true_and] using h

noncomputable def botProdEquiv {A D : Type*} [Group A] [Group D]
    (B : Subgroup D) : (⊥ : Subgroup A).prod B ≃* B where
  toFun x := ⟨x.val.2, x.property.2⟩
  invFun x := ⟨(1,x), ⟨rfl,x.property⟩⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext x.property.1.symm rfl
  right_inv x := rfl
  map_mul' x y := rfl

/-- The alternating local join, in its prescribed product coordinates. -/
noncomputable def alternatingJoinEquiv {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 (S3 × D)) (B : Subgroup D)
    (hB : normalizer (B : Set D) = B) (eB : B ≃* A4)
    (hn : (P : Subgroup (S3 × D)) ≤
      normalizer ((⊥ : Subgroup S3).prod B : Set (S3 × D))) :
    ↥((⊥ : Subgroup S3).prod B ⊔ (P : Subgroup (S3 × D))) ≃* C2 × A4 := by
  have hr := rightProjection_le_normalizer (P : Subgroup (S3 × D)) B hn
  rw [hB] at hr
  have he : (⊥ : Subgroup S3).prod B ⊔ (P : Subgroup (S3 × D)) =
      (P.map (MonoidHom.fst S3 D)).prod B := by
    conv_lhs => rw [sylow_prod P]
    rw [prod_sup_prod, bot_sup_eq, sup_eq_left.mpr hr]
  exact (MulEquiv.subgroupCongr he).trans ((prodEquiv _ _).trans
    ((mulEquivOfPrimeCardEq (left_sylow_card P)
      (by simp [Nat.card_eq_fintype_card, Fintype.card_perm] : Nat.card C2 = 2)).prodCongr eB))

private theorem s3_core_join_sylow (P : Sylow 2 S3) :
    pCore 3 S3 ⊔ (P : Subgroup S3) = ⊤ := by
  have hp : Nat.card P = 2 := by
    have h := P.card_eq_multiplicity
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial,
      show (6 : ℕ).factorization 2 = 1 from by
      rw [show 6 = 2 ^ 1 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
        Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)],
    show (120 : ℕ).factorization 2 = 3 from by
      rw [show 120 = 2 ^ 3 * 15 from rfl, Nat.factorization_mul (by decide) (by decide),
        Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]] at h
    exact h
  have hd₃ : 3 ∣ Nat.card ↥(pCore 3 S3 ⊔ (P : Subgroup S3)) := by
    simpa only [s3_threeCore_card] using card_dvd_of_le
      (show pCore 3 S3 ≤ pCore 3 S3 ⊔ (P : Subgroup S3) from le_sup_left)
  have hd₂ : 2 ∣ Nat.card ↥(pCore 3 S3 ⊔ (P : Subgroup S3)) := by
    simpa only [hp] using card_dvd_of_le
      (show (P : Subgroup S3) ≤ pCore 3 S3 ⊔ (P : Subgroup S3) from le_sup_right)
  have hd : 6 ∣ Nat.card ↥(pCore 3 S3 ⊔ (P : Subgroup S3)) := by
    simpa using (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) hd₂ hd₃)
  apply eq_top_of_card_eq
  have hcard : Nat.card S3 = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hcard]
  exact Nat.dvd_antisymm (hcard ▸ (pCore 3 S3 ⊔ (P : Subgroup S3)).card_subgroup_dvd_card) hd

/-- The symmetric local overlap, retaining the prescribed normalizer of B.
The orders here are the actual A₄ and S₄ orders, not an overlap hypothesis. -/
noncomputable def symmetricJoinEquiv (P : Sylow 2 (S3 × Equiv.Perm (Fin 5)))
    (B : Subgroup (Equiv.Perm (Fin 5))) (eB : B ≃* A4)
    (eN : normalizer (B : Set (Equiv.Perm (Fin 5))) ≃* S4)
    (hn : (P : Subgroup (S3 × Equiv.Perm (Fin 5))) ≤
      normalizer ((⊥ : Subgroup S3).prod B : Set (S3 × Equiv.Perm (Fin 5)))) :
    ↥(pCore 3 (S3 × Equiv.Perm (Fin 5)) ⊔ (⊥ : Subgroup S3).prod B ⊔
      (P : Subgroup (S3 × Equiv.Perm (Fin 5)))) ≃* S3 × S4 := by
  let Q := P.mapSurjective (f := MonoidHom.snd S3 (Equiv.Perm (Fin 5)))
    (fun x => ⟨(1,x),rfl⟩)
  let R := P.mapSurjective (f := MonoidHom.fst S3 (Equiv.Perm (Fin 5)))
    (fun x => ⟨(x,1),rfl⟩)
  have hQ : Nat.card Q = 8 := by
    have h := Q.card_eq_multiplicity
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial,
      show (6 : ℕ).factorization 2 = 1 from by
      rw [show 6 = 2 ^ 1 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
        Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)],
    show (120 : ℕ).factorization 2 = 3 from by
      rw [show 120 = 2 ^ 3 * 15 from rfl, Nat.factorization_mul (by decide) (by decide),
        Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]] at h
    exact h
  have hB : Nat.card B = 12 := by
    rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hN : Nat.card ↥(normalizer (B : Set (Equiv.Perm (Fin 5)))) = 24 := by
    rw [Nat.card_congr eN.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hle : B ⊔ (Q : Subgroup (Equiv.Perm (Fin 5))) ≤ normalizer (B : Set _) :=
    sup_le le_normalizer (rightProjection_le_normalizer _ B hn)
  have he : B ⊔ (Q : Subgroup (Equiv.Perm (Fin 5))) = normalizer (B : Set _) := by
    apply eq_of_le_of_card_ge hle
    have hd₁ : 12 ∣ Nat.card ↥(B ⊔ (Q : Subgroup (Equiv.Perm (Fin 5)))) :=
      hB ▸ card_dvd_of_le (show B ≤ B ⊔ (Q : Subgroup _) from le_sup_left)
    have hd₂ : 8 ∣ Nat.card ↥(B ⊔ (Q : Subgroup (Equiv.Perm (Fin 5)))) :=
      hQ ▸ card_dvd_of_le (show (Q : Subgroup _) ≤ B ⊔ (Q : Subgroup _) from le_sup_right)
    have hd : 24 ∣ Nat.card ↥(B ⊔ (Q : Subgroup (Equiv.Perm (Fin 5)))) := by
      simpa only [show Nat.lcm 12 8 = 24 from by decide] using Nat.lcm_dvd hd₁ hd₂
    rw [hN]
    exact Nat.le_of_dvd Nat.card_pos hd
  have himage : pCore 3 (S3 × Equiv.Perm (Fin 5)) ⊔ (⊥ : Subgroup S3).prod B ⊔
      (P : Subgroup (S3 × Equiv.Perm (Fin 5))) =
      (⊤ : Subgroup S3).prod (normalizer (B : Set _)) := by
    rw [pCore_prod, s5_threeCore_eq_bot]
    conv_lhs => rw [sylow_prod P]
    rw [prod_sup_prod, sup_bot_eq, bot_sup_eq, prod_sup_prod]
    change (pCore 3 S3 ⊔ (R : Subgroup S3)).prod (B ⊔ (Q : Subgroup _)) = _
    rw [s3_core_join_sylow, he]
  exact (MulEquiv.subgroupCongr himage).trans
    ((prodEquiv _ _).trans (topEquiv.prodCongr eN))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
