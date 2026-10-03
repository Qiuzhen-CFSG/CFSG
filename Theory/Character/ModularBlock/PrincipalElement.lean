module

public import Theory.Character.ModularBlock.PrincipalSelector
public import Theory.Character.ModularBlock.CentralCoefficient
public import Theory.Character.ModularBlock.CentralIdempotentSupport

/-!
# Principal-block idempotence and weak orthogonality

The localized selector's zero-or-one irreducible scalar actions prove
idempotence by character expansion, which also computes its coefficients.
Its augmentation is one because it acts identically on the trivial
representation. Injective scalar extension transfers these statements to
the integral localization.

Over that local characteristic-zero domain, two is a nonunit. The central
idempotent support theorem kills every nontrivial involution coefficient.
The character coefficient formula therefore gives Feit IV.7.2, weak block
orthogonality in the form needed by Glauberman's Z* argument.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BlockOrthogonality.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.BlockOrthogonality

open BlockPreliminaries PrincipalBlockConstruction

attribute [local instance] Fintype.ofFinite

universe u v w

variable {G : Type u} [Group G] [Finite G]

/-- Coefficient formula for the principal-block element (Feit IV.7.1). -/
theorem principalBlockElement_coeff
    (d : PrincipalCongruenceBlockData G) (g : G) :
    (principalBlockElement d).coeff g =
      (Nat.card G : ℂ)⁻¹ *
        ∑ i ∈ d.block,
          d.chi i (ConjClasses.mk (1 : G)) *
            d.chi i (ConjClasses.mk g⁻¹) := by
  classical
  have hcoeff := coeff_eq_inv_card_mul_sum_scalar_degree_character
    d.chi d.complete (principalBlockElement d)
    (principalBlockElement_comm d)
    (fun i : d.I => if i ∈ d.block then 1 else 0)
    (by
      intro i n ρ hρ
      exact principalBlockElement_action d i ρ hρ)
    g
  rw [hcoeff]
  congr 1
  simp

theorem principalBlockElement_isIdempotent
    (d : PrincipalCongruenceBlockData G) :
    IsIdempotentElem (principalBlockElement d) := by
  classical
  let e := principalBlockElement d
  have hecenter : e ∈ Set.center (MonoidAlgebra ℂ G) :=
    principalBlockElement_mem_center d
  have hdiffcenter : e * e - e ∈ Set.center (MonoidAlgebra ℂ G) := by
    rw [sub_eq_add_neg]
    exact Set.add_mem_center (Set.mul_mem_center hecenter hecenter)
      (Set.neg_mem_center hecenter)
  have hdiffcomm : ∀ a : MonoidAlgebra ℂ G,
      a * (e * e - e) = (e * e - e) * a :=
    (Semigroup.mem_center_iff.mp hdiffcenter)
  have haction : ∀ i : d.I, ∀ {n : ℕ}
      (ρ : Representation ℂ G (Fin n → ℂ)),
      d.chi i = (characterClassFunction ρ) →
      ρ.asAlgebraHom (e * e - e) =
        (0 : ℂ) • (1 : Module.End ℂ (Fin n → ℂ)) := by
    intro i n ρ hρ
    rw [map_sub, map_mul]
    change ρ.asAlgebraHom (principalBlockElement d) *
        ρ.asAlgebraHom (principalBlockElement d) -
      ρ.asAlgebraHom (principalBlockElement d) =
        (0 : ℂ) • (1 : Module.End ℂ (Fin n → ℂ))
    rw [principalBlockElement_action d i ρ hρ]
    by_cases hi : i ∈ d.block <;> simp [hi]
  have hdiffzero : e * e - e = 0 := by
    ext g
    change (e * e - e).coeff g = 0
    have hcoeff := coeff_eq_inv_card_mul_sum_scalar_degree_character
      d.chi d.complete (e * e - e) hdiffcomm
      (fun _i : d.I => (0 : ℂ)) haction g
    simpa using hcoeff
  change e * e = e
  exact sub_eq_zero.mp hdiffzero

theorem localizedPrincipalBlockElement_isIdempotent
    (d : PrincipalCongruenceBlockData G) :
    IsIdempotentElem (localizedPrincipalBlockElement d) := by
  change localizedPrincipalBlockElement d * localizedPrincipalBlockElement d =
    localizedPrincipalBlockElement d
  apply localizedGroupAlgebraToComplex_injective d
  rw [map_mul]
  change principalBlockElement d * principalBlockElement d =
    principalBlockElement d
  exact principalBlockElement_isIdempotent d

/-- The principal-block selector has augmentation one: it acts as the
identity on the trivial representation. -/
theorem principalBlockElement_sum_coeff_eq_one
    (d : PrincipalCongruenceBlockData G) :
    ∑ g : G, (principalBlockElement d).coeff g = 1 := by
  let rho0 : Representation ℂ G (Fin 1 → ℂ) :=
    Representation.trivial ℂ G (Fin 1 → ℂ)
  have hchar : d.chi d.principal = (characterClassFunction rho0) := by
    rw [d.principal_eq]
    ext C
    rcases ConjClasses.exists_rep C with ⟨g, rfl⟩
    change 1 = rho0.character g
    simp [rho0, Representation.character]
  have haction := principalBlockElement_action
    d d.principal rho0 hchar
  have haction' : rho0.asAlgebraHom (principalBlockElement d) = 1 := by
    simpa using haction
  have hone := congrArg
    (fun f : Module.End ℂ (Fin 1 → ℂ) => f (fun _ => 1) 0) haction'
  have hactionSum (a : MonoidAlgebra ℂ G) :
      (rho0.asAlgebraHom a (fun _ => 1)) 0 = ∑ g : G, a.coeff g := by
    induction a using MonoidAlgebra.induction_linear with
    | zero =>
        change 0 = ∑ _g : G, (0 : ℂ)
        simp
    | add a b ha hb =>
        simp only [map_add, LinearMap.add_apply, Pi.add_apply, ha, hb]
        change (∑ g : G, a.coeff g) + (∑ g : G, b.coeff g) =
          ∑ g : G, (a.coeff g + b.coeff g)
        rw [Finset.sum_add_distrib]
    | single g r => simp
  rw [hactionSum] at hone
  exact hone

/-- The integral-localized principal-block selector also has augmentation
one.  This is detected after embedding the localization into `ℂ`. -/
theorem localizedPrincipalBlockElement_sum_coeff_eq_one
    (d : PrincipalCongruenceBlockData G) :
    ∑ g : G, (localizedPrincipalBlockElement d).coeff g = 1 := by
  apply localizationToComplex_injective d
  rw [map_one, map_sum]
  calc
    ∑ g : G, localizationToComplex d.primeIdeal
        ((localizedPrincipalBlockElement d).coeff g) =
        ∑ g : G, (principalBlockElement d).coeff g := by
      apply Finset.sum_congr rfl
      intro g _hg
      exact (principalBlockElement_coeff_eq_localized d g).symm
    _ = 1 := principalBlockElement_sum_coeff_eq_one d

/-- The weak block-orthogonality conclusion reduced to the local support
statement for the constructed integral idempotent. -/
theorem block_sum_eq_zero_of_localized_coeff_eq_zero
    (d : PrincipalCongruenceBlockData G)
    (s : G) (hs : IsInvolution s)
    (hsupport : (localizedPrincipalBlockElement d).coeff s = 0) :
    ∑ i ∈ d.block,
      d.chi i (ConjClasses.mk s) *
        d.chi i (ConjClasses.mk (1 : G)) = 0 := by
  classical
  have hs_inv : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs.2)
  have hezero : (principalBlockElement d).coeff s = 0 := by
    rw [principalBlockElement_coeff_eq_localized, hsupport]
    exact map_zero (localizationToComplex d.primeIdeal)
  have hformula := principalBlockElement_coeff d s
  rw [hs_inv, hezero] at hformula
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos ( α := G)).ne'
  have hsum :
      ∑ i ∈ d.block,
        d.chi i (ConjClasses.mk (1 : G)) *
          d.chi i (ConjClasses.mk s) = 0 := by
    exact (mul_eq_zero.mp hformula.symm).resolve_left (inv_ne_zero hcard)
  calc
    (∑ i ∈ d.block,
        d.chi i (ConjClasses.mk s) *
          d.chi i (ConjClasses.mk (1 : G))) =
      ∑ i ∈ d.block,
        d.chi i (ConjClasses.mk (1 : G)) *
          d.chi i (ConjClasses.mk s) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm]
    _ = 0 := hsum

theorem localizedPrincipalBlockElement_coeff_involution_eq_zero
    (d : PrincipalCongruenceBlockData G)
    (s : G) (hs : IsInvolution s) :
    (localizedPrincipalBlockElement d).coeff s = 0 := by
  exact CentralIdempotentSupport.coeff_involution_eq_zero
    (two_not_isUnit_cyclotomicOrderAtPrime d) s hs.1
    (by simpa [pow_two] using hs.2)
    (localizedPrincipalBlockElement d)
    (localizedPrincipalBlockElement_isIdempotent d)
    (localizedPrincipalBlockElement_mem_center d)

theorem weak_block_orthogonality_of_localized_support
    (d : PrincipalCongruenceBlockData G)
    (hsupport : ∀ s : G, IsInvolution s →
      (localizedPrincipalBlockElement d).coeff s = 0) :
    ∀ s : G, IsInvolution s →
      ∑ i ∈ d.block,
        d.chi i (ConjClasses.mk s) *
          d.chi i (ConjClasses.mk (1 : G)) = 0 := by
  intro s hs
  exact block_sum_eq_zero_of_localized_coeff_eq_zero d s hs
    (hsupport s hs)

/-- Weak orthogonality for the principal ordinary congruence block
(Feit IV.7.2), in the exact form required by the `Z*` argument. -/
theorem weak_block_orthogonality
    (d : PrincipalCongruenceBlockData G) :
    ∀ s : G, IsInvolution s →
      ∑ i ∈ d.block,
        d.chi i (ConjClasses.mk s) *
          d.chi i (ConjClasses.mk (1 : G)) = 0 :=
  weak_block_orthogonality_of_localized_support d
    (localizedPrincipalBlockElement_coeff_involution_eq_zero d)


end ModularBlock.BlockOrthogonality
