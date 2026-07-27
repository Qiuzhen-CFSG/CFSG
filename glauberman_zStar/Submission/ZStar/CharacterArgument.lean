import Submission.BenderSuzuki.External.Suzuki.VI.theorem_1_8
import Submission.FeitThompson.Representation.Divisibility
import Submission.FeitThompson.Representation.SimpleCriteria
import Submission.FeitThompson.PFsection6.Basic
import Submission.ZStar.OddCommutators

/-!
# The ordinary-character part of Glauberman's Z*-argument

This file formalizes the parts of Glauberman's proof that use only ordinary
complex characters:

* multiplication of two conjugacy-class sums;
* the normalized character identity obtained when the character is constant
  on all products of elements from the two classes;
* the resulting `chi(t) = ± chi(1)` calculation;
* the final `2 = 0` contradiction from the two principal-block section
  orthogonality equations;
* the group-theoretic kernel step used to exclude the positive sign.

No Brauer characters or block theory are assumed here.  The later modular
layer only has to supply Glauberman's constancy and section-orthogonality
statements for the principal `2`-block.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace CharacterArgument

universe u v

attribute [local instance] Fintype.ofFinite

/-- The principal ordinary character, viewed as a function on conjugacy
classes. -/
def ordinaryPrincipalCharacter
    (G : Type u) [Group G] : Representation.ClassFunction G :=
  fun _ => 1

@[simp] theorem ordinaryPrincipalCharacter_apply
    {G : Type u} [Group G] (C : ConjClasses G) :
    ordinaryPrincipalCharacter G C = 1 := rfl

/-- An irreducible ordinary character has nonzero degree. -/
theorem irreducibleCharacter_degree_ne_zero
    {G : Type u} [Group G] [Finite G]
    (chi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi) :
    chi (ConjClasses.mk (1 : G)) ≠ 0 := by
  rcases hchi.1 with ⟨n, rho, rfl⟩
  have hirr : Representation.IsIrreducible rho :=
    (Representation.irreducible_iff_character_norm_one (ρ := rho)).2 hchi.2
  letI : Representation.IsIrreducible rho := hirr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := rho)
  have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
    (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
  have hdim_ne : (Module.finrank ℂ (Fin n → ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdim_pos)
  change rho.character 1 ≠ 0
  simpa [Representation.character] using hdim_ne

/-- The representation affording a nonprincipal irreducible character has
proper kernel.

This is the conjugacy-class-function wrapper around the existing Peterfalvi
kernel criterion
`Section6.not_subgroupInKernel_top_of_irreducible_ne_principal`. -/
theorem representationKernel_ne_top_of_irreducibleCharacter_ne_principal
    {G : Type u} [Group G] [Finite G]
    (chi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi)
    (hne : chi ≠ ordinaryPrincipalCharacter G)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ))
    (hchar : chi = Representation.characterClassFunction rho) :
    rho.ker ≠ ⊤ := by
  have hirr : Representation.IsIrreducible rho := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [hchar] using hchi.2
  have hrho_ne : rho.character ≠ Section1.principalCharacter G := by
    intro hrho
    apply hne
    rw [hchar]
    ext C
    rcases ConjClasses.exists_rep C with ⟨g, rfl⟩
    change rho.character g = 1
    rw [hrho]
    rfl
  have hrhoIrr : Section1.IsIrreducibleCharacterOnGroup rho.character :=
    ⟨n, rho, hirr, rfl⟩
  have hnotTop :=
    Section6.not_subgroupInKernel_top_of_irreducible_ne_principal
      hrhoIrr hrho_ne
  intro hker
  apply hnotTop
  apply (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
    rho ⊤).2
  intro g
  have hg : (g : G) ∈ rho.ker := by
    rw [hker]
    exact g.2
  exact MonoidHom.mem_ker.mp hg

private def conjugateCarrierEquiv
    {G : Type u} [Group G] (C : ConjClasses G) (c : G) :
    C.carrier ≃ C.carrier where
  toFun x := ⟨c * x.1 * c⁻¹, by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact ((ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨c, rfl⟩)).symm).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
  invFun x := ⟨c⁻¹ * x.1 * (c⁻¹)⁻¹, by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact ((ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨c⁻¹, rfl⟩)).symm).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

private theorem pairCount_eq_of_isConj
    {G : Type u} [Group G] [Finite G]
    (Ci Cj : ConjClasses G) {x y : G} (hxy : IsConj x y) :
    Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = x} =
      Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = y} := by
  rcases isConj_iff.mp hxy with ⟨c, hc⟩
  let ei := conjugateCarrierEquiv Ci c
  let ej := conjugateCarrierEquiv Cj c
  apply Nat.card_congr
  exact {
    toFun := fun p => ⟨(ei p.1.1, ej p.1.2), by
      dsimp [ei, ej, conjugateCarrierEquiv]
      have hprod :
          c * p.1.1.1 * c⁻¹ * (c * p.1.2.1 * c⁻¹) = c * x * c⁻¹ := by
        simpa [mul_assoc] using congrArg (fun z : G => c * z * c⁻¹) p.2
      exact hprod.trans hc⟩
    invFun := fun p => ⟨(ei.symm p.1.1, ej.symm p.1.2), by
      dsimp [ei, ej, conjugateCarrierEquiv]
      simpa [mul_assoc] using
        congrArg (fun z : G => c⁻¹ * z * (c⁻¹)⁻¹) (p.2.trans hc.symm)⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> simp [ei, ej]
    right_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> simp [ei, ej] }

/-- The coefficient of the class `Ck` in the product of the class sums of
`Ci` and `Cj`.  It is the number of factorizations of one (hence every)
element of `Ck` as a product of an element of `Ci` and an element of `Cj`. -/
def classProductCoeff
    {G : Type u} [Group G] [Finite G]
    (Ci Cj Ck : ConjClasses G) : ℕ :=
  Nat.card {p : Ci.carrier × Cj.carrier //
    p.1.1 * p.2.1 = Quotient.out Ck}

/-- `classProductCoeff` is independent of the representative chosen in its
output conjugacy class. -/
theorem classProductCoeff_spec
    {G : Type u} [Group G] [Finite G]
    (Ci Cj Ck : ConjClasses G) (x : G) (hx : x ∈ Ck.carrier) :
    classProductCoeff Ci Cj Ck =
      Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = x} := by
  apply pairCount_eq_of_isConj
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  exact (Quotient.out_eq Ck).trans
    (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm

/-- Counting all pairs in two conjugacy classes by the conjugacy class of
their product gives the weighted class-multiplication identity. -/
theorem classProductCoeff_weighted_sum
    {G : Type u} [Group G] [Finite G]
    (Ci Cj : ConjClasses G) :
    (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) =
      (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
        (fun Ck =>
          (classProductCoeff Ci Cj Ck : ℂ) * (Nat.card Ck.carrier : ℂ)) := by
  classical
  let rho0 : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ
  letI : Representation.IsIrreducible rho0 :=
    Representation.trivial_complex_irreducible
  have hmul := Representation.classSumScalar_mul_eq_sum_of_coefficients
    (ρ := rho0) (a := classProductCoeff)
    (hdata := fun i j s x hx => classProductCoeff_spec i j s x hx) Ci Cj
  have hscalar (C : ConjClasses G) :
      Representation.classSumScalar (ρ := rho0) C =
        (Nat.card C.carrier : ℂ) := by
    rw [Representation.classSumScalar_eq_card_mul_character_div
      (ρ := rho0) C
      (ConjClasses.mem_carrier_iff_mk_eq.mpr (Quotient.out_eq C))]
    simp [rho0, Representation.character]
  simpa [hscalar] using hmul

/-- If an irreducible character is constant on every product of a conjugate
of `u` with a conjugate of `v`, then its normalized values multiply:

`(chi(u) / chi(1)) (chi(v) / chi(1)) = chi(uv) / chi(1)`.

This is the class-sum calculation in Step (VI) of Glauberman's proof. -/
theorem characterRatio_mul_eq_of_classProducts_constant
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho]
    (u v : G)
    (hconstant : ∀ x : G, x ∈ (ConjClasses.mk u).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk v).carrier →
        rho.character (x * y) = rho.character (u * v)) :
    (rho.character u / rho.character 1) *
        (rho.character v / rho.character 1) =
      rho.character (u * v) / rho.character 1 := by
  classical
  let Ci : ConjClasses G := ConjClasses.mk u
  let Cj : ConjClasses G := ConjClasses.mk v
  have hsupport (Ck : ConjClasses G)
      (hk : classProductCoeff Ci Cj Ck ≠ 0) :
      rho.character (Quotient.out Ck) = rho.character (u * v) := by
    have hne : Nonempty
        {p : Ci.carrier × Cj.carrier //
          p.1.1 * p.2.1 = Quotient.out Ck} :=
      (Nat.card_ne_zero.mp hk).1
    let p := Classical.choice hne
    have hp := hconstant p.1.1.1 (by simpa [Ci] using p.1.1.2)
      p.1.2.1 (by simpa [Cj] using p.1.2.2)
    simpa [p.2] using hp
  have hmul := Representation.classSumScalar_mul_eq_sum_of_coefficients
    (ρ := rho) (a := classProductCoeff)
    (hdata := fun i j s x hx => classProductCoeff_spec i j s x hx) Ci Cj
  have hCi :
      Representation.classSumScalar (ρ := rho) Ci =
        (Nat.card Ci.carrier : ℂ) * rho.character u / rho.character 1 := by
    exact Representation.classSumScalar_eq_card_mul_character_div
      (ρ := rho) Ci ConjClasses.mem_carrier_mk
  have hCj :
      Representation.classSumScalar (ρ := rho) Cj =
        (Nat.card Cj.carrier : ℂ) * rho.character v / rho.character 1 := by
    exact Representation.classSumScalar_eq_card_mul_character_div
      (ρ := rho) Cj ConjClasses.mem_carrier_mk
  have hrhs :
      (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
          (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
            Representation.classSumScalar (ρ := rho) Ck) =
        (rho.character (u * v) / rho.character 1) *
          (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
            (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
              (Nat.card Ck.carrier : ℂ)) := by
    calc
      (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
          (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
            Representation.classSumScalar (ρ := rho) Ck) =
          (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
            (fun Ck => (rho.character (u * v) / rho.character 1) *
              ((classProductCoeff Ci Cj Ck : ℂ) *
                (Nat.card Ck.carrier : ℂ))) := by
            refine Finset.sum_congr rfl ?_
            intro Ck _
            by_cases hk : classProductCoeff Ci Cj Ck = 0
            · simp [hk]
            · rw [Representation.classSumScalar_eq_card_mul_character_div
                (ρ := rho) Ck
                (ConjClasses.mem_carrier_iff_mk_eq.mpr (Quotient.out_eq Ck)),
                hsupport Ck hk]
              ring
      _ = (rho.character (u * v) / rho.character 1) *
          (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
            (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
              (Nat.card Ck.carrier : ℂ)) := by
            rw [Finset.mul_sum]
  rw [hCi, hCj] at hmul
  have hmul' := hmul.trans hrhs
  rw [← classProductCoeff_weighted_sum Ci Cj] at hmul'
  letI : Nonempty Ci.carrier :=
    ⟨⟨u, by simpa [Ci] using (ConjClasses.mem_carrier_mk (a := u))⟩⟩
  letI : Nonempty Cj.carrier :=
    ⟨⟨v, by simpa [Cj] using (ConjClasses.mem_carrier_mk (a := v))⟩⟩
  have hCi_ne : (Nat.card Ci.carrier : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Ci.carrier)).ne'
  have hCj_ne : (Nat.card Cj.carrier : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Cj.carrier)).ne'
  apply mul_left_cancel₀ (mul_ne_zero hCi_ne hCj_ne)
  calc
    ((Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ)) *
          ((rho.character u / rho.character 1) *
            (rho.character v / rho.character 1)) =
        ((Nat.card Ci.carrier : ℂ) * rho.character u / rho.character 1) *
          ((Nat.card Cj.carrier : ℂ) * rho.character v / rho.character 1) := by
            ring
    _ = (rho.character (u * v) / rho.character 1) *
          ((Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ)) := hmul'
    _ = ((Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ)) *
          (rho.character (u * v) / rho.character 1) := by ring

/-- Class-function wrapper for `characterRatio_mul_eq_of_classProducts_constant`. -/
theorem irreducibleCharacterRatio_mul_eq_of_classProducts_constant
    {G : Type u} [Group G] [Finite G]
    (chi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi)
    (u v : G)
    (hconstant : ∀ x : G, x ∈ (ConjClasses.mk u).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk v).carrier →
        chi (ConjClasses.mk (x * y)) = chi (ConjClasses.mk (u * v))) :
    (chi (ConjClasses.mk u) / chi (ConjClasses.mk (1 : G))) *
        (chi (ConjClasses.mk v) / chi (ConjClasses.mk (1 : G))) =
      chi (ConjClasses.mk (u * v)) / chi (ConjClasses.mk (1 : G)) := by
  rcases hchi.1 with ⟨n, rho, rfl⟩
  have hirr : Representation.IsIrreducible rho :=
    (Representation.irreducible_iff_character_norm_one (ρ := rho)).2 hchi.2
  letI : Representation.IsIrreducible rho := hirr
  refine characterRatio_mul_eq_of_classProducts_constant rho u v ?_
  intro x hx y hy
  change rho.character (x * y) = rho.character (u * v)
  exact hconstant x hx y hy

/-- The elementary algebra at the end of Glauberman Step (VI): the two
normalized product identities and a nonzero value at `s` force the value at
`t` to be either the degree or its negative. -/
theorem value_eq_degree_or_neg_degree_of_ratio_relations
    {a b c d : ℂ} (hd : d ≠ 0) (hb : b ≠ 0)
    (h1 : (a / d) * (b / d) = c / d)
    (h2 : (a / d) * (c / d) = b / d) :
    a = d ∨ a = -d := by
  field_simp [hd] at h1 h2
  have hsquare_mul : b * a ^ 2 = b * d ^ 2 := by
    calc
      b * a ^ 2 = a * (a * b) := by ring
      _ = a * (d * c) := by rw [h1]
      _ = d * (a * c) := by ring
      _ = d * (d * b) := by rw [h2]
      _ = b * d ^ 2 := by ring
  have hsquare : a ^ 2 = d ^ 2 := mul_left_cancel₀ hb hsquare_mul
  have hfactor : (a - d) * (a + d) = 0 := by
    calc
      (a - d) * (a + d) = a ^ 2 - d ^ 2 := by ring
      _ = 0 := by rw [hsquare, sub_self]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The purely algebraic final contradiction in Glauberman Step (VII).

`valueS`, `valueT`, and `degree` are the values at `s`, `t`, and `1` of the
ordinary characters in a proposed principal block.  The distinguished index
`principal` is the principal character. -/
theorem false_of_principalSectionOrthogonality
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Finset I) (principal : I)
    (valueS valueT degree : I → ℂ)
    (hprincipal_mem : principal ∈ B)
    (hprincipalS : valueS principal = 1)
    (hprincipalT : valueT principal = 1)
    (hprincipalDegree : degree principal = 1)
    (hnegative : ∀ i ∈ B, i ≠ principal → valueS i ≠ 0 →
      valueT i = -degree i)
    (horthT : ∑ i ∈ B, valueS i * valueT i = 0)
    (horthOne : ∑ i ∈ B, valueS i * degree i = 0) : False := by
  let f : I → ℂ := fun i => valueS i * (valueT i + degree i)
  have hsum_zero : ∑ i ∈ B, f i = 0 := by
    calc
      (∑ i ∈ B, f i) =
          (∑ i ∈ B, valueS i * valueT i) +
            ∑ i ∈ B, valueS i * degree i := by
              simp only [f, mul_add, Finset.sum_add_distrib]
      _ = 0 := by rw [horthT, horthOne, add_zero]
  have hsum_two : ∑ i ∈ B, f i = 2 := by
    rw [Finset.sum_eq_single principal]
    · norm_num [f, hprincipalS, hprincipalT, hprincipalDegree]
    · intro i hi hne
      by_cases his : valueS i = 0
      · simp [f, his]
      · simp [f, hnegative i hi hne his]
    · exact fun hnot => (hnot hprincipal_mem).elim
  have : (2 : ℂ) = 0 := hsum_two.symm.trans hsum_zero
  norm_num at this

/-- A weaker-orthogonality variant of the final contradiction in Glauberman
Step (VII).

Here `valueS` and `valueTS` are the character values at `s` and `t * s`.
The ordinary class-sum argument makes these values negatives of one another
for every nonprincipal character.  Consequently weak block orthogonality of
each involution against the identity is enough: after adding the two sums,
only the principal character contributes, and it contributes `2`. -/
theorem false_of_principalWeakSectionOrthogonality
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Finset I) (principal : I)
    (valueS valueTS degree : I → ℂ)
    (hprincipal_mem : principal ∈ B)
    (hprincipalS : valueS principal = 1)
    (hprincipalTS : valueTS principal = 1)
    (hprincipalDegree : degree principal = 1)
    (hnegativeTS : ∀ i ∈ B, i ≠ principal → valueTS i = -valueS i)
    (horthS : ∑ i ∈ B, valueS i * degree i = 0)
    (horthTS : ∑ i ∈ B, valueTS i * degree i = 0) :
    False := by
  let f : I → ℂ := fun i => (valueS i + valueTS i) * degree i
  have hsum_zero : ∑ i ∈ B, f i = 0 := by
    calc
      (∑ i ∈ B, f i) =
          (∑ i ∈ B, valueS i * degree i) +
            ∑ i ∈ B, valueTS i * degree i := by
              simp only [f, add_mul, Finset.sum_add_distrib]
      _ = 0 := by rw [horthS, horthTS, add_zero]
  have hsum_two : ∑ i ∈ B, f i = 2 := by
    rw [Finset.sum_eq_single principal]
    · norm_num [f, hprincipalS, hprincipalTS, hprincipalDegree]
    · intro i hi hne
      simp [f, hnegativeTS i hi hne]
    · exact fun hnot => (hnot hprincipal_mem).elim
  have : (2 : ℂ) = 0 := hsum_two.symm.trans hsum_zero
  norm_num at this

/-- An element whose square is one and whose order is odd is the identity. -/
theorem eq_one_of_sq_eq_one_of_orderOf_odd
    {G : Type*} [Group G] {x : G}
    (hsq : x * x = 1) (hodd : Odd (orderOf x)) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    simpa [pow_two] using hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
  · exact orderOf_eq_one_iff.mp hone
  · rw [htwo] at hodd
    norm_num at hodd

/-- Kernel step in Glauberman Step (VI).

If `t` is central in a normal subgroup containing it, and all commutators with
`t` have odd order, then `t` is already central in the whole group.  Applied
to the kernel of an irreducible representation, this excludes
`chi(t) = chi(1)` once induction has made `t` central in that kernel. -/
theorem mem_center_of_normal_central_and_odd_commutators
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) (hN : N.Normal) (t : G)
    (htI : IsInvolution t) (htN : t ∈ N)
    (htCentralN : ∀ n : G, n ∈ N → n * t = t * n)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹))) :
    t ∈ Subgroup.center G := by
  have ht_inv : t⁻¹ = t :=
    inv_eq_self_of_sq_eq_one (by simpa [pow_two] using htI.2)
  rw [Subgroup.mem_center_iff]
  intro g
  let u : G := g * t * g⁻¹
  have huN : u ∈ N := by
    exact hN.conj_mem t htN g
  have huI : IsInvolution u := by
    simpa [u] using OddCommutators.isInvolution_conjugate htI g
  have hut_comm : u * t = t * u := htCentralN u huN
  have hut_sq : (u * t) * (u * t) = 1 := by
    calc
      (u * t) * (u * t) = (u * u) * (t * t) := by
        rw [mul_assoc, ← mul_assoc t u t, ← hut_comm]
        simp only [mul_assoc]
      _ = 1 := by
        have hu_sq : u * u = 1 := by simpa [pow_two] using huI.2
        have ht_sq : t * t = 1 := by simpa [pow_two] using htI.2
        rw [hu_sq, ht_sq, mul_one]
  have hut_odd : Odd (orderOf (u * t)) := by
    simpa [u, ht_inv, mul_assoc] using hodd g
  have hut_one : u * t = 1 :=
    eq_one_of_sq_eq_one_of_orderOf_odd hut_sq hut_odd
  have hu_eq_t : u = t := by
    calc
      u = (u * t) * t⁻¹ := by simp [mul_assoc]
      _ = t := by rw [hut_one, one_mul, ht_inv]
  calc
    g * t = (g * t * g⁻¹) * g := by group
    _ = u * g := by rfl
    _ = t * g := by rw [hu_eq_t]

/-- The induction/kernel adapter in Glauberman Step (VI).

For a nonprincipal irreducible character, equality `chi(t) = chi(1)` puts
`t` in the proper representation kernel by Suzuki VI.1.8(ii).  If the
induction hypothesis centralizes `t` in every proper normal subgroup, the
odd-commutator calculation then centralizes `t` in all of `G`, contradicting
the chosen counterexample. -/
theorem irreducibleCharacter_value_ne_degree_of_properNormal_centrality
    {G : Type u} [Group G] [Finite G]
    (chi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi)
    (hne : chi ≠ ordinaryPrincipalCharacter G)
    (t : G) (htI : IsInvolution t)
    (htNotCentral : t ∉ Subgroup.center G)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (hproperCentral : ∀ (N : Subgroup G), N.Normal → N ≠ ⊤ → t ∈ N →
      ∀ n : G, n ∈ N → n * t = t * n) :
    chi (ConjClasses.mk t) ≠ chi (ConjClasses.mk (1 : G)) := by
  rcases hchi.1 with ⟨n, rho, hchar⟩
  have hirr : Representation.IsIrreducible rho :=
    (Representation.irreducible_iff_character_norm_one (ρ := rho)).2 (by
      simpa [hchar] using hchi.2)
  letI : Representation.IsIrreducible rho := hirr
  have hker_ne : rho.ker ≠ ⊤ :=
    representationKernel_ne_top_of_irreducibleCharacter_ne_principal
      chi hchi hne rho hchar
  intro hvalue
  have hrho_value : rho.character t = rho.character 1 := by
    rw [hchar] at hvalue
    change rho.character t = rho.character 1 at hvalue
    exact hvalue
  have htker : t ∈ rho.ker :=
    (BenderSuzuki.External.Suzuki.VI.suzuki_ch6_theorem_1_8_ii rho t).1
      hrho_value
  have hker_normal : rho.ker.Normal := inferInstance
  have htCentralKer : ∀ n : G, n ∈ rho.ker → n * t = t * n :=
    hproperCentral rho.ker hker_normal hker_ne htker
  exact htNotCentral (mem_center_of_normal_central_and_odd_commutators
    rho.ker hker_normal t htI htker htCentralKer hodd)

end CharacterArgument

end Submission.ZStar
