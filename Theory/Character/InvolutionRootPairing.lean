module
public import Theory.Character.InvolutionRootInduction
public import Theory.Character.ClassSumFormula
public import Theory.GroupTheory.InvolutionRootPairs

/-!
# Induction paired with actual involution factorizations

For an involution t, a function on C_G(t) supported on roots of t has the same
pairing with the number of ordered involution factorizations before and after
induction. Frobenius reciprocity reduces this to the fact that both factors of
a root centralize t. The character coefficient of the pair-count function is
|G|⁻¹ χ(I)²/χ(1), where I consists of all elements of order exactly two.
Thus applying the pairing to irreducible expansions gives Wong's identity.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2, J. Austral. Math. Soc. 4 (1964), 90–112, Lemma 4(iii),
p. 98, DOI 10.1017/S1446788700022771.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

namespace Theory.Character

/-- The actual number of ordered pairs of involutions whose product is `g`. -/
@[expose] public def involutionPairCount {G : Type*} [Group G] (g : G) : ℕ :=
  Nat.card {p : G × G // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = g}

/-- Character sum over all actual involutions, excluding the identity. -/
@[expose] public def involutionSum {G : Type*} [Group G] [Finite G] (χ : ClassFunction G) : ℂ :=
  ∑ x : {x : G // orderOf x = 2}, χ x

/-- The pair count is conjugacy invariant. -/
public theorem involutionPairCount_isClassFunction {G : Type*} [Group G] :
    IsClassFunction (fun g : G => (involutionPairCount g : ℂ)) := by
  intro g x
  apply congrArg Nat.cast
  unfold involutionPairCount
  apply Nat.card_congr
  let e := MulAut.conj x
  refine {
    toFun := fun p => ⟨(e.symm p.1.1, e.symm p.1.2),
      (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans p.2.1,
      (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans p.2.2.1, ?_⟩
    invFun := fun p => ⟨(e p.1.1, e p.1.2),
      (orderOf_injective e.toMonoidHom e.injective _).trans p.2.1,
      (orderOf_injective e.toMonoidHom e.injective _).trans p.2.2.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [← map_mul, p.2.2.2]
    change e.symm (e g) = g
    exact e.symm_apply_apply g
  · rw [← map_mul, p.2.2.2]
    rfl
  · intro p
    apply Subtype.ext
    exact Prod.ext (e.apply_symm_apply _) (e.apply_symm_apply _)
  · intro p
    apply Subtype.ext
    exact Prod.ext (e.symm_apply_apply _) (e.symm_apply_apply _)

/-- The ambient and centralizer pair-count functions agree at every root. -/
public theorem involutionPairCount_centralizer_of_root
    {G : Type*} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    (a : Subgroup.centralizer ({t} : Set G)) (ha : t ∈ Subgroup.zpowers (a : G)) :
    involutionPairCount (a : G) = involutionPairCount a := by
  rw [involutionPairCount, involution_pair_card_eq_centralizer_of_root t a ht ha,
    involutionPairCount]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun p =>
    and_congr_right fun _ => and_congr_right fun _ =>
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Wong's involution-root identity as a pairing against the actual count. -/
public theorem scalarProduct_induced_involutionPairCount
    {G : Type*} [Group G] [Fintype G] (t : G) (ht : orderOf t = 2)
    (Φ : ClassFunction (Subgroup.centralizer ({t} : Set G)))
    (hΦ : ∀ a : Subgroup.centralizer ({t} : Set G),
      t ∉ Subgroup.zpowers (a : G) → Φ a = 0) :
    scalarProduct G (inducedClassFunction (Subgroup.centralizer ({t} : Set G)) Φ)
      (fun g => (involutionPairCount g : ℂ)) =
    scalarProduct (Subgroup.centralizer ({t} : Set G)) Φ
      (fun a => (involutionPairCount a : ℂ)) := by
  rw [scalarProduct_inducedClassFunction _ _ involutionPairCount_isClassFunction]
  unfold scalarProduct
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  by_cases ha : t ∈ Subgroup.zpowers (a : G)
  · rw [involutionPairCount_centralizer_of_root t ht a ha]
  · rw [hΦ a ha, zero_mul, zero_mul]

variable {G : Type*} [Group G] [Fintype G]

private def involutionSet : Finset G := Finset.univ.filter (fun x : G => orderOf x = 2)

private def involutionClassSum : MonoidAlgebra ℂ G :=
  ∑ x ∈ involutionSet (G := G), MonoidAlgebra.single x 1

private lemma involutionClassSum_coeff (x : G) :
    (involutionClassSum (G := G)).coeff x = if orderOf x = 2 then 1 else 0 := by
  classical
  simp [involutionClassSum, involutionSet, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]

omit [Fintype G] in
private lemma orderOf_inverse_mul_shift (g x : G) : orderOf (g⁻¹ * x) = orderOf (x * g⁻¹) := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (g⁻¹ * x)
  simpa [MulAut.conj_apply, mul_assoc] using h.symm

private lemma involutionClassSum_comm (a : MonoidAlgebra ℂ G) :
    a * involutionClassSum = involutionClassSum * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
        involutionClassSum_coeff]
      rw [orderOf_inverse_mul_shift, mul_comm]

private lemma sum_character_involution_products (n : ℕ) (ρ : Representation ℂ G (Fin n → ℂ))
    [Representation.IsIrreducible ρ] :
    (∑ x : {x : G // orderOf x = 2}, ∑ y : {x : G // orderOf x = 2},
      ρ.character (x * y)) =
      (∑ x : {x : G // orderOf x = 2}, ρ.character x) ^ 2 / ρ.character 1 := by
  classical
  obtain ⟨a, ha⟩ := centralElementIntertwiner_eq_scalar ρ
    (involutionClassSum (G := G)) involutionClassSum_comm
  have hs : ρ.asAlgebraHom (involutionClassSum (G := G)) =
      ∑ x : {x : G // orderOf x = 2}, ρ x := by
    rw [involutionClassSum, map_sum]
    simp only [Representation.asAlgebraHom_single_one]
    exact Finset.sum_subtype _ (by simp [involutionSet]) _
  have htrace : (∑ x : {x : G // orderOf x = 2}, ρ.character x) =
      a * (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    have hh := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) ha
    rw [hs] at hh
    simpa [map_sum, Representation.character, map_smul, LinearMap.trace_one] using hh
  have htrace2 : (∑ x : {x : G // orderOf x = 2},
      ∑ y : {x : G // orderOf x = 2}, ρ.character (x * y)) =
      a ^ 2 * (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    have hh := congrArg (fun A => LinearMap.trace ℂ (Fin n → ℂ) (A * A)) ha
    rw [hs, Finset.sum_mul_sum] at hh
    simpa [map_sum, ← map_mul, Representation.character, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, smul_smul, map_smul, LinearMap.trace_one, pow_two] using hh
  have hdeg : ρ.character 1 = (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    simp [Representation.character]
  let : Nontrivial (Fin n → ℂ) := irreducible_nontrivial ρ
  have hdim : (Module.finrank ℂ (Fin n → ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Fin n → ℂ)).ne'
  rw [htrace, htrace2, hdeg]
  field_simp

private lemma sum_involutionPairCount_mul (χ : ClassFunction G) :
    (∑ g : G, (involutionPairCount g : ℂ) * χ g) =
      ∑ p : {x : G // orderOf x = 2} × {x : G // orderOf x = 2}, χ (p.1 * p.2) := by
  classical
  unfold involutionPairCount
  let I := {x : G // orderOf x = 2}
  let f : I × I → G := fun p => p.1 * p.2
  have hc (g : G) :
      Nat.card {p : G × G // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = g} =
        Nat.card {p : I × I // f p = g} := by
    apply Nat.card_congr
    exact {
      toFun := fun p => ⟨(⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1⟩), p.2.2.2⟩
      invFun := fun p => ⟨(p.1.1, p.1.2), p.1.1.2, p.1.2.2, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ g : G, ∑ _p : {p : I × I // f p = g}, χ g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hc]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ = _ := Fintype.sum_fiberwise' f χ

/-- Pairing any function with the pair count is the normalized sum of its
values on all ordered products of involutions. This also permits direct
counting through a quotient without identifying local irreducible characters. -/
public theorem scalarProduct_involutionPairCount_eq_sum (f : ClassFunction G) :
    scalarProduct G f (fun a => (involutionPairCount a : ℂ)) =
      (Nat.card G : ℂ)⁻¹ *
        ∑ p : {a : G // orderOf a = 2} × {a : G // orderOf a = 2}, f (p.1 * p.2) := by
  unfold scalarProduct
  simp only [star_natCast, mul_comm (f _)]
  rw [sum_involutionPairCount_mul]

/-- The coefficient of an irreducible character in the actual involution-pair
count, in the orientation linear in the character. -/
public theorem scalarProduct_irreducible_involutionPairCount
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G χ (fun g => (involutionPairCount g : ℂ)) =
      (Nat.card G : ℂ)⁻¹ * involutionSum χ ^ 2 / χ 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  let : Representation.IsIrreducible ρ := hρ
  unfold scalarProduct
  simp only [star_natCast, mul_comm (ρ.character _)]
  rw [sum_involutionPairCount_mul, Fintype.sum_prod_type,
    sum_character_involution_products]
  simp only [involutionSum, mul_div_assoc]
  -- The subtype sum in `involutionSum` uses the canonical finite enumeration.
  congr
  exact Subsingleton.elim _ _

/-- Pairing an irreducible expansion with actual involution pairs gives the
weighted degree expression. No integrality assumption on coefficients is needed. -/
public theorem scalarProduct_expansion_involutionPairCount
    {ι : Type*} [Fintype ι] (χ : ι → ClassFunction G)
    (hχ : ∀ i, IsIrreducibleCharacter (χ i)) (c : ι → ℂ) :
    scalarProduct G (∑ i, c i • χ i) (fun g => (involutionPairCount g : ℂ)) =
      (Nat.card G : ℂ)⁻¹ * ∑ i, involutionSum (χ i) ^ 2 * c i / χ i 1 := by
  have hsum :
      scalarProduct G (∑ i, c i • χ i) (fun g => (involutionPairCount g : ℂ)) =
        ∑ i, c i * scalarProduct G (χ i) (fun g => (involutionPairCount g : ℂ)) := by
    simp only [scalarProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_natCast]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  simp_rw [scalarProduct_irreducible_involutionPairCount _ (hχ _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Wong, Lemma 4(iii): induction of a function supported on roots of an
involution preserves the weighted involution-sum degree expression.

The two finite irreducible expansions may have arbitrary complex coefficients;
in particular this applies to the integer expansions of generalized characters.
The sums `involutionSum` range over all elements of order exactly two in the
respective groups. -/
public theorem involutionRoots_degree_identity
    {G : Type*} [Group G] [Fintype G] (t : G) (ht : orderOf t = 2)
    (Φ : ClassFunction (Subgroup.centralizer ({t} : Set G)))
    (hΦ : ∀ a : Subgroup.centralizer ({t} : Set G),
      t ∉ Subgroup.zpowers (a : G) → Φ a = 0)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι → ClassFunction G)
    (φ : κ → ClassFunction (Subgroup.centralizer ({t} : Set G)))
    (hχ : ∀ i, IsIrreducibleCharacter (χ i))
    (hφ : ∀ j, IsIrreducibleCharacter (φ j))
    (c : ι → ℂ) (b : κ → ℂ)
    (hc : inducedClassFunction (Subgroup.centralizer ({t} : Set G)) Φ = ∑ i, c i • χ i)
    (hb : Φ = ∑ j, b j • φ j) :
    (Nat.card G : ℂ)⁻¹ * ∑ i, involutionSum (χ i) ^ 2 * c i / χ i 1 =
      (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ)⁻¹ *
        ∑ j, involutionSum (φ j) ^ 2 * b j / φ j 1 := by
  have h := scalarProduct_induced_involutionPairCount t ht Φ hΦ
  rw [hc, hb, scalarProduct_expansion_involutionPairCount χ hχ c,
    scalarProduct_expansion_involutionPairCount φ hφ b] at h
  exact h

end Theory.Character
