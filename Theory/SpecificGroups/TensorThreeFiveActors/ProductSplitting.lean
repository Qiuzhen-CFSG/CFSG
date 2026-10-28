module

public import Theory.SpecificGroups.TensorThreeFiveActors.Reduction
public import Theory.GroupTheory.PPerfectHom

/-!
# Independent cubic actors in S₃ × D

For any finite group D, a Sylow-normalized two-perfect subgroup A with
|A/O₂(A)| = 3 lies in exactly one factor. The sign homomorphism kills the
first odd coordinates. If that projection is nontrivial, commutation with
an independent Sylow transposition extracts a generator of the pure cubic
axis. This normal axis has order three; its quotient in A has the order of
O₂(A), and hence is a two-group. Two-perfectness makes A equal to the axis.
If the first projection is trivial, the second projection is an actual
isomorphism and transports the intrinsic two-core quotient.

The final corollaries discharge the splitting premise in the two tensor
models. The five-point calculation `FactorActors` remains explicit; its
independent producer and the source assembly are separate from this module.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 14.4.10(1),
printed p.1010/PDF p.1027, under the models of 14.4.2(5), printed p.1006/PDF p.1023.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.TensorThreeFiveActors

private theorem transposition_cubic_commutator :
    ∀ (t a : Equiv.Perm (Fin 3)), t ≠ 1 → t ^ 2 = 1 →
    Equiv.Perm.sign a = 1 → t * a * t⁻¹ * a⁻¹ = a := by decide +kernel

variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
private theorem first_sign_eq_one (A : Subgroup (Equiv.Perm (Fin 3) × D))
    (hp : IsPPerfect 2 A) (x : A) : Equiv.Perm.sign x.val.1 = 1 := by
  let f : A →* ℤˣ := Equiv.Perm.sign.comp ((MonoidHom.fst _ _).comp A.subtype)
  have hu : IsPGroup 2 ℤˣ := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_eq_fintype_card]; decide)
  exact DFunLike.congr_fun (hp.hom_eq_one_of_isPGroup hu f) x

private theorem exists_first_involution (Q : Sylow 2 (Equiv.Perm (Fin 3) × D)) :
    ∃ t : Equiv.Perm (Fin 3), (t, 1) ∈ Q ∧ t ≠ 1 ∧ t ^ 2 = 1 := by
  let P := Q.mapSurjective (f := MonoidHom.fst (Equiv.Perm (Fin 3)) D)
    (fun t => ⟨(t, 1), rfl⟩)
  have hcard : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [show 6 = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hne : (P : Subgroup (Equiv.Perm (Fin 3))) ≠ ⊥ := by
    intro h
    have hh : Nat.card P = 1 := by rw [h]; exact card_bot
    omega
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ P, t ≠ 1 := by
    by_contra! h
    exact hne (P.toSubgroup.eq_bot_iff_forall.mpr h)
  refine ⟨t, ?_, ht1, ?_⟩
  · change (t, (1 : D)) ∈ (Q : Subgroup (Equiv.Perm (Fin 3) × D))
    rw [sylow_eq_prod Q]
    exact ⟨ht, (Q.map (MonoidHom.snd _ _)).one_mem⟩
  · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [← hcard]; exact P.orderOf_dvd_natCard ht)

private theorem cubic_axis_le_of_first_ne_one
    (Q : Sylow 2 (Equiv.Perm (Fin 3) × D))
    (A : Subgroup (Equiv.Perm (Fin 3) × D))
    (hn : (Q : Subgroup (Equiv.Perm (Fin 3) × D)) ≤
      normalizer (A : Set (Equiv.Perm (Fin 3) × D)))
    (hp : IsPPerfect 2 A) (x : A) (hx : x.val.1 ≠ 1) :
    (pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D) ≤ A := by
  obtain ⟨t, ht, ht1, ht2⟩ := exists_first_involution Q
  have hsign := first_sign_eq_one A hp x
  have haxis : (x.val.1, (1 : D)) ∈ A := by
    have hcj := (hn ht x.val).mp x.property
    have hm := A.mul_mem hcj (A.inv_mem x.property)
    have he : (t, (1 : D)) * x.val * (t, (1 : D))⁻¹ * x.val⁻¹ =
        (x.val.1, (1 : D)) := by
      apply Prod.ext
      · exact transposition_cubic_commutator t x.val.1 ht1 ht2 hsign
      · simp
    rwa [he] at hm
  have hg : zpowers (x.val.1, (1 : D)) =
      (pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D) := by
    have hmem : (x.val.1, (1 : D)) ∈
        (pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D) := by
      rw [s3_threeCore_eq]
      exact ⟨Equiv.Perm.mem_alternatingGroup.mpr hsign, rfl⟩
    have hc : Nat.card ((pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D)) = 3 := by
      rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
        TensorThreeFive.s3_threeCore_card, card_bot, mul_one]
    have ho : orderOf (x.val.1, (1 : D)) = 3 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd _
        (hc ▸ ((pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D)).orderOf_dvd_natCard hmem)
        with ho | ho
      · exact (hx (congrArg Prod.fst (orderOf_eq_one_iff.mp ho))).elim
      · exact ho
    exact eq_of_le_of_card_ge (zpowers_le_of_mem hmem) (by rw [Nat.card_zpowers, ho, hc])
  rw [← hg]
  exact zpowers_le_of_mem haxis

private theorem eq_cubic_axis_of_le
    (A : Subgroup (Equiv.Perm (Fin 3) × D)) (hp : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hle : (pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D) ≤ A) :
    A = (pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D) := by
  let C := (pCore 3 (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup D)
  have hC : Nat.card (C.subgroupOf A) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
      TensorThreeFive.s3_threeCore_card, card_bot, mul_one]
  have hq : IsPGroup 2 (A ⧸ C.subgroupOf A) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    apply IsPGroup.of_card (n := n)
    have h₁ := (C.subgroupOf A).card_eq_card_quotient_mul_card_subgroup
    have h₂ := (pCore 2 A).card_eq_card_quotient_mul_card_subgroup
    rw [hC] at h₁
    rw [hc, hn] at h₂
    omega
  exact le_antisymm (subgroupOf_eq_top.mp (hp _ inferInstance hq)) hle

omit [Finite D] in
private theorem second_factor_of_first_trivial
    (A : Subgroup (Equiv.Perm (Fin 3) × D)) (hp : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hfirst : ∀ x : A, x.val.1 = 1) :
    ∃ B : Subgroup D, A = (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod B ∧
      IsPPerfect 2 B ∧ Nat.card (B ⧸ pCore 2 B) = 3 := by
  let q := MonoidHom.snd (Equiv.Perm (Fin 3)) D
  let B := A.map q
  have hi : Function.Injective (q.subgroupMap A) := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact (hfirst x).trans (hfirst y).symm
    · exact congrArg Subtype.val h
  let e : A ≃* B := MulEquiv.ofBijective (q.subgroupMap A) ⟨hi, q.subgroupMap_surjective A⟩
  refine ⟨B, ?_, hp.of_surjective e.toMonoidHom e.surjective, ?_⟩
  · ext x
    constructor
    · intro hx
      exact ⟨hfirst ⟨x, hx⟩, mem_map_of_mem q hx⟩
    · rintro ⟨hx, y, hy, he⟩
      have hxy : x = y := by
        apply Prod.ext
        · exact hx.trans (hfirst ⟨y, hy⟩).symm
        · exact he.symm
      exact hxy ▸ hy
  · rw [← Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hc

/-- A Sylow-normalized two-perfect cubic actor in S₃ × D lies in one factor.
No catalogue or placement hypothesis is needed for the finite second factor. -/
theorem productSplitting (D : Type*) [Group D] [Finite D] : ProductSplitting D := by
  intro Q A hn hp hc
  by_cases hfirst : ∀ x : A, x.val.1 = 1
  · exact Or.inr (second_factor_of_first_trivial A hp hc hfirst)
  · push Not at hfirst
    obtain ⟨x, hx⟩ := hfirst
    exact Or.inl (eq_cubic_axis_of_le A hp hc (cubic_axis_le_of_first_ne_one Q A hn hp x hx))

/-- Independent-factor splitting for the symmetric five-point tensor model. -/
theorem s5_productSplitting : ProductSplitting (Equiv.Perm (Fin 5)) :=
  productSplitting _

/-- Independent-factor splitting for the alternating five-point tensor model. -/
theorem a5_productSplitting : ProductSplitting (alternatingGroup (Fin 5)) :=
  productSplitting _

/-- The S₃ × S₅ actor dichotomy, with only the independent five-point calculation
remaining. This supplies the splitting premise of `product_actors_of_factors`. -/
theorem s3_s5_actors_of_factorActors
    (hfive : FactorActors (Equiv.Perm (Fin 5)))
    (Q : Sylow 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)))
    (A : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)))
    (hn : (Q : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) ≤
      normalizer (A : Set (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) ∨
      A = solvableResidual (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) ⊓ normalizer
        (((Q : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) ⊓
          solvableResidual (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) :
          Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) :
          Set (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) :=
  product_actors_of_factors TensorThreeFive.s5_threeCore_eq_bot
    s5_productSplitting hfive Q A hn hp hc

/-- The S₃ × A₅ actor dichotomy, with only the independent five-point calculation
remaining. The residual and Sylow-relative normalizer are literal subgroups. -/
theorem s3_a5_actors_of_factorActors
    (hfive : FactorActors (alternatingGroup (Fin 5)))
    (Q : Sylow 2 (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)))
    (A : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)))
    (hn : (Q : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5))) ≤
      normalizer (A : Set (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5))))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)) ∨
      A = solvableResidual (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)) ⊓ normalizer
        (((Q : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5))) ⊓
          solvableResidual (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)) :
          Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5))) :
          Set (Equiv.Perm (Fin 3) × alternatingGroup (Fin 5))) :=
  product_actors_of_factors TensorThreeFive.a5_threeCore_eq_bot
    a5_productSplitting hfive Q A hn hp hc

end Theory.SpecificGroups.TensorThreeFiveActors

end
