import Submission.ZStar.BlockOrthogonality
import Submission.ZStar.CyclotomicDVR
import Mathlib.LinearAlgebra.PID

/-!
# Integral isotypic lattices in the regular representation

The primitive ordinary character projector usually has a denominator
`|G|`.  Multiplying it by `|G|` gives an integral central element `q` with
`q ^ 2 = |G| q`.  Its right ideal is therefore a finite free lattice over
the local cyclotomic DVR.  This file develops the generic scaled-projector
trace calculation needed to use that lattice without choosing an integral
model of an arbitrary affording representation.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar
namespace IsotypicLattice

universe u v

attribute [local instance] Fintype.ofFinite

open PrincipalBlockConstruction

private noncomputable def centralIntertwiner
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    Representation.IntertwiningMap rho rho where
  toLinearMap := rho.asAlgebraHom z
  isIntertwining' g := by
    rw [← Representation.asAlgebraHom_single_one (ρ := rho) g]
    change rho.asAlgebraHom z *
        rho.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) =
      rho.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) *
        rho.asAlgebraHom z
    rw [← map_mul, ← map_mul]
    exact congrArg rho.asAlgebraHom
      (hz (MonoidAlgebra.single g (1 : ℂ))).symm

private lemma centralIntertwiner_eq_scalar
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho]
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    ∃ a : ℂ, rho.asAlgebraHom z = a • (1 : Module.End ℂ V) := by
  classical
  have hfin : Module.finrank ℂ
      (Representation.IntertwiningMap rho rho) = 1 :=
    (Representation.irreducible_iff_end_dimension_one (ρ := rho)).1
      inferInstance
  haveI : Nontrivial V := Representation.irreducible_nontrivial (ρ := rho)
  have hone_ne_zero :
      (1 : Representation.IntertwiningMap rho rho) ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    apply hx
    simpa using congrArg
      (fun f : Representation.IntertwiningMap rho rho ↦ f x) h
  obtain ⟨a, ha⟩ : ∃ a : ℂ,
      a • (1 : Representation.IntertwiningMap rho rho) =
        centralIntertwiner rho z hz :=
    (finrank_eq_one_iff_of_nonzero'
      (K := ℂ) (V := Representation.IntertwiningMap rho rho)
      (1 : Representation.IntertwiningMap rho rho) hone_ne_zero).mp hfin
      (centralIntertwiner rho z hz)
  refine ⟨a, ?_⟩
  ext x
  simpa [centralIntertwiner] using congrArg
    (fun f : Representation.IntertwiningMap rho rho ↦ f x) ha.symm

/-- Trace of an arbitrary group-algebra element in a representation. -/
theorem groupAlgebra_trace
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (z : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (rho.asAlgebraHom z) =
      ∑ g : G, z.coeff g * rho.character g := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      change (∑ g : G, x.coeff g * rho.character g) +
          (∑ g : G, y.coeff g * rho.character g) =
        ∑ g : G, (x.coeff g + y.coeff g) * rho.character g
      simp only [add_mul, Finset.sum_add_distrib]
  | single g r =>
      have hmap : rho.asAlgebraHom (MonoidAlgebra.single g r) =
          r • rho g := by
        rw [show (MonoidAlgebra.single g r : MonoidAlgebra ℂ G) =
          r • MonoidAlgebra.single g 1 by simp, map_smul,
          Representation.asAlgebraHom_single_one]
      rw [hmap, map_smul]
      change r * rho.character g =
        ∑ x : G, (MonoidAlgebra.single g r).coeff x * rho.character x
      rw [Finset.sum_eq_single g]
      · change r * rho.character g =
          (Finsupp.single g r) g * rho.character g
        simp
      · intro x _hx hxg
        change (Finsupp.single g r) x * rho.character x = 0
        simp [hxg]
      · simp

/-- Orthogonality inside a fixed complete irreducible character family. -/
theorem completeFamily_inner
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → Representation.ClassFunction G)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (i j : I) :
    Representation.classFunctionInner (chi i) (chi j) =
      if i = j then 1 else 0 := by
  classical
  rcases Representation.completeFamily_form_basis hchi with ⟨b, hb⟩
  rw [← Representation.completeFamily_basis_repr_eq_inner
    hchi b hb (chi i) j]
  rw [← hb i, b.repr_self_apply]

/-- A coefficient function constant under conjugation defines a central
group-algebra element. -/
theorem mem_center_of_coeff_conj_invariant
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (a : MonoidAlgebra R G)
    (ha : ∀ x y : G, a (x * y * x⁻¹) = a y) :
    a ∈ Set.center (MonoidAlgebra R G) := by
  classical
  rw [Semigroup.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      rw [MonoidAlgebra.single_mul_apply,
        MonoidAlgebra.mul_single_apply]
      have hcoeff : a (g⁻¹ * x) = a (x * g⁻¹) := by
        simpa [mul_assoc] using ha g⁻¹ (x * g⁻¹)
      rw [hcoeff]
      exact mul_comm _ _

theorem mapRingHom_mem_center
    {R S : Type u} {G : Type v}
    [CommRing R] [CommRing S] [Group G]
    (f : R →+* S) (a : MonoidAlgebra R G)
    (ha : a ∈ Set.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapRingHom G f a ∈
      Set.center (MonoidAlgebra S G) := by
  rw [Semigroup.mem_center_iff] at ha ⊢
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single g r =>
      let x : MonoidAlgebra R G := MonoidAlgebra.single g 1
      have hx := congrArg (MonoidAlgebra.mapRingHom G f) (ha x)
      rw [map_mul, map_mul] at hx
      have hsingle :
          (MonoidAlgebra.single g r : MonoidAlgebra S G) =
            r • MonoidAlgebra.single g 1 := by simp
      rw [hsingle, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun z : MonoidAlgebra S G ↦ r • z)
        (by simpa [x] using hx)

theorem mapRingHom_injective
    {R S : Type u} {G : Type v}
    [CommRing R] [CommRing S] [Group G]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (MonoidAlgebra.mapRingHom G f) := by
  intro a b hab
  ext g
  apply hf
  simpa only [MonoidAlgebra.mapRingHom_apply] using
    congrArg (fun z : MonoidAlgebra S G ↦ z g) hab

section CharacterProjector

variable {G : Type u} [Group G] [Finite G]

private instance principalPrime_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

/-- The canonical embedding of the localized cyclotomic order into `ℂ`. -/
noncomputable def localizationToComplex
    (d : PrincipalCongruenceBlockData G) :
    Localization.AtPrime d.primeIdeal →+* ℂ := by
  let A := Representation.cyclotomicOrder d.eta
  let f : A →+* ℂ := Subring.subtype A
  exact IsLocalization.lift
    (M := d.primeIdeal.primeCompl)
    (S := Localization.AtPrime d.primeIdeal)
    (g := f) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro hy
      apply y.2
      have hyA : (y.1 : ℂ) = 0 := by simpa [f] using hy
      have hyzero : y.1 = 0 := Subtype.ext hyA
      rw [hyzero]
      exact d.primeIdeal.zero_mem)

@[simp] theorem localizationToComplex_algebraMap
    (d : PrincipalCongruenceBlockData G)
    (a : Representation.cyclotomicOrder d.eta) :
    localizationToComplex d
        (algebraMap _ (Localization.AtPrime d.primeIdeal) a) = (a : ℂ) := by
  apply IsLocalization.lift_eq

theorem localizationToComplex_injective
    (d : PrincipalCongruenceBlockData G) :
    Function.Injective (localizationToComplex d) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    d.primeIdeal.primeCompl (localizationToComplex d)).2
  intro x y
  constructor
  · exact fun h ↦ congrArg (localizationToComplex d) h
  · intro h
    have hcoe : (x : ℂ) = (y : ℂ) := by
      simpa only [localizationToComplex_algebraMap] using h
    have hxy : x = y := Subtype.ext hcoe
    rw [hxy]

/-- An irreducible character value in the chosen cyclotomic order. -/
noncomputable def characterValueInCyclotomicOrder
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    Representation.cyclotomicOrder d.eta := by
  refine ⟨d.chi i (ConjClasses.mk g), ?_⟩
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  rw [hrho]
  exact Representation.representation_character_mem_cyclotomicOrder
    d.eta_spec rho g

@[simp] theorem coe_characterValueInCyclotomicOrder
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    ((characterValueInCyclotomicOrder d i g :
      Representation.cyclotomicOrder d.eta) : ℂ) =
        d.chi i (ConjClasses.mk g) :=
  rfl

/-- The denominator-cleared primitive character projector. -/
noncomputable def characterProjectorNumerator
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) G :=
  MonoidAlgebra.ofCoeff
    ((Finsupp.equivFunOnFinite :
      (G →₀ Localization.AtPrime d.primeIdeal) ≃
        (G → Localization.AtPrime d.primeIdeal)).symm
      (fun g ↦
        algebraMap (Representation.cyclotomicOrder d.eta)
          (Localization.AtPrime d.primeIdeal)
          (characterValueInCyclotomicOrder d i 1 *
            characterValueInCyclotomicOrder d i g⁻¹)))

@[simp] theorem characterProjectorNumerator_apply
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    characterProjectorNumerator d i g =
      algebraMap (Representation.cyclotomicOrder d.eta)
        (Localization.AtPrime d.primeIdeal)
        (characterValueInCyclotomicOrder d i 1 *
          characterValueInCyclotomicOrder d i g⁻¹) := by
  classical
  change (MonoidAlgebra.ofCoeff
      ((Finsupp.equivFunOnFinite :
        (G →₀ Localization.AtPrime d.primeIdeal) ≃
          (G → Localization.AtPrime d.primeIdeal)).symm
        (fun x ↦
          algebraMap (Representation.cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (characterValueInCyclotomicOrder d i 1 *
              characterValueInCyclotomicOrder d i x⁻¹)))).coeff g = _
  rw [MonoidAlgebra.coeff_ofCoeff]
  simpa using congrFun (Equiv.apply_symm_apply
    (Finsupp.equivFunOnFinite :
      (G →₀ Localization.AtPrime d.primeIdeal) ≃
        (G → Localization.AtPrime d.primeIdeal)) _) g

theorem characterProjectorNumerator_mem_center
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    characterProjectorNumerator d i ∈
      Set.center
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) := by
  apply mem_center_of_coeff_conj_invariant
  intro x y
  simp only [characterProjectorNumerator_apply]
  congr 2
  apply Subtype.ext
  change d.chi i (ConjClasses.mk (x * y * x⁻¹)⁻¹) =
    d.chi i (ConjClasses.mk y⁻¹)
  apply congrArg (d.chi i)
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  apply isConj_iff.mpr
  refine ⟨x⁻¹, ?_⟩
  simp [mul_assoc]

noncomputable def complexCharacterProjectorNumerator
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff
    ((Finsupp.equivFunOnFinite : (G →₀ ℂ) ≃ (G → ℂ)).symm
      (fun g ↦ d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk g⁻¹)))

@[simp] theorem complexCharacterProjectorNumerator_apply
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    complexCharacterProjectorNumerator d i g =
      d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk g⁻¹) := by
  classical
  change (MonoidAlgebra.ofCoeff
      ((Finsupp.equivFunOnFinite : (G →₀ ℂ) ≃ (G → ℂ)).symm
        (fun x ↦ d.chi i (ConjClasses.mk (1 : G)) *
          d.chi i (ConjClasses.mk x⁻¹)))).coeff g = _
  rw [MonoidAlgebra.coeff_ofCoeff]
  simpa using congrFun (Equiv.apply_symm_apply
    (Finsupp.equivFunOnFinite : (G →₀ ℂ) ≃ (G → ℂ)) _) g

theorem map_characterProjectorNumerator
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    MonoidAlgebra.mapRingHom G (localizationToComplex d)
        (characterProjectorNumerator d i) =
      complexCharacterProjectorNumerator d i := by
  classical
  ext x
  rw [MonoidAlgebra.mapRingHom_apply,
    characterProjectorNumerator_apply,
    complexCharacterProjectorNumerator_apply]
  simp

theorem complexCharacterProjectorNumerator_mem_center
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    complexCharacterProjectorNumerator d i ∈
      Set.center (MonoidAlgebra ℂ G) := by
  rw [← map_characterProjectorNumerator d i]
  exact mapRingHom_mem_center (localizationToComplex d)
    (characterProjectorNumerator d i)
    (characterProjectorNumerator_mem_center d i)

private theorem star_character_eq_inv
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    star (d.chi i (ConjClasses.mk g)) =
      d.chi i (ConjClasses.mk g⁻¹) := by
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  rw [hrho]
  exact (Representation.representation_character_inv_eq_star_character
    rho g).symm

/-- The numerator projector acts by `|G|` on its chosen irreducible and by
zero on every other irreducible. -/
theorem complexCharacterProjectorNumerator_action
    (d : PrincipalCongruenceBlockData G) (i j : d.I)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ))
    (hrho : d.chi j = rho.characterClassFunction) :
    rho.asAlgebraHom (complexCharacterProjectorNumerator d i) =
      (if i = j then (Nat.card G : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  have hirr : Representation.IsIrreducible rho := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [← hrho] using (d.complete.1 j).2
  letI : Representation.IsIrreducible rho := hirr
  let q := complexCharacterProjectorNumerator d i
  have hqcenter : q ∈ Set.center (MonoidAlgebra ℂ G) :=
    complexCharacterProjectorNumerator_mem_center d i
  obtain ⟨lambda, hlambda⟩ := centralIntertwiner_eq_scalar rho q
    (Semigroup.mem_center_iff.mp hqcenter)
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hinner := completeFamily_inner d.chi d.complete j i
  rw [Representation.classFunctionInner] at hinner
  simp_rw [star_character_eq_inv d i] at hinner
  have hsum :
      ∑ g : G,
          d.chi j (ConjClasses.mk g) *
            d.chi i (ConjClasses.mk g⁻¹) =
        (Nat.card G : ℂ) * (if j = i then 1 else 0) := by
    apply (mul_left_cancel₀ hcard)
    calc
      (Nat.card G : ℂ) *
          ∑ g : G,
            d.chi j (ConjClasses.mk g) *
              d.chi i (ConjClasses.mk g⁻¹) =
          (Nat.card G : ℂ) ^ 2 *
            ((Nat.card G : ℂ)⁻¹ *
              ∑ g : G,
                d.chi j (ConjClasses.mk g) *
                  d.chi i (ConjClasses.mk g⁻¹)) := by
            field_simp [hcard]
      _ = (Nat.card G : ℂ) ^ 2 *
          (if j = i then 1 else 0) := by rw [hinner]
      _ = (Nat.card G : ℂ) *
          ((Nat.card G : ℂ) * (if j = i then 1 else 0)) := by ring
  have htraceQ :
      LinearMap.trace ℂ (Fin n → ℂ) (rho.asAlgebraHom q) =
        d.chi i (ConjClasses.mk (1 : G)) *
          ((Nat.card G : ℂ) * (if j = i then 1 else 0)) := by
    rw [groupAlgebra_trace]
    change (∑ g : G,
        complexCharacterProjectorNumerator d i g * rho.character g) = _
    simp_rw [complexCharacterProjectorNumerator_apply]
    have hchar (g : G) : rho.character g =
        d.chi j (ConjClasses.mk g) := by
      rw [hrho]
      rfl
    simp_rw [hchar]
    calc
      (∑ g : G,
          d.chi i (ConjClasses.mk (1 : G)) *
            d.chi i (ConjClasses.mk g⁻¹) *
              d.chi j (ConjClasses.mk g)) =
          d.chi i (ConjClasses.mk (1 : G)) *
            ∑ g : G,
              d.chi j (ConjClasses.mk g) *
                d.chi i (ConjClasses.mk g⁻¹) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g _
            ring
      _ = d.chi i (ConjClasses.mk (1 : G)) *
          ((Nat.card G : ℂ) * (if j = i then 1 else 0)) := by
            rw [hsum]
  have hdegree : d.chi j (ConjClasses.mk (1 : G)) = (n : ℂ) := by
    rw [hrho]
    change rho.character 1 = (n : ℂ)
    simp [Representation.character]
  have hn : (n : ℂ) ≠ 0 := by
    have hpos : 0 < n := by
      haveI : Nontrivial (Fin n → ℂ) :=
        Representation.irreducible_nontrivial (ρ := rho)
      simpa using
        ((Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2
          inferInstance)
    exact_mod_cast hpos.ne'
  rw [hlambda] at htraceQ
  simp only [map_smul, LinearMap.trace_one, smul_eq_mul] at htraceQ
  have hfinrank : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  rw [hfinrank] at htraceQ
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl] at htraceQ
    rw [hdegree] at htraceQ
    have hlambda_eq : lambda = (Nat.card G : ℂ) := by
      apply (mul_right_cancel₀ hn)
      simpa [mul_comm, mul_assoc] using htraceQ
    simpa [hlambda_eq] using hlambda
  · have hji : j ≠ i := Ne.symm hij
    simp only [if_neg hij, if_neg hji, mul_zero] at htraceQ
    have hlambda0 : lambda = 0 := by
      apply (mul_right_cancel₀ hn)
      simpa using htraceQ
    simpa [q, hij, hlambda0] using hlambda

/-- The denominator-cleared primitive character projector satisfies the
scaled idempotence relation `q² = |G| q` over `ℂ`. -/
theorem complexCharacterProjectorNumerator_mul_self
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    complexCharacterProjectorNumerator d i *
        complexCharacterProjectorNumerator d i =
      (Nat.card G : ℂ) • complexCharacterProjectorNumerator d i := by
  classical
  let q := complexCharacterProjectorNumerator d i
  have hqcenter : q ∈ Set.center (MonoidAlgebra ℂ G) :=
    complexCharacterProjectorNumerator_mem_center d i
  let qz : Subring.center (MonoidAlgebra ℂ G) := ⟨q, hqcenter⟩
  let zz : Subring.center (MonoidAlgebra ℂ G) :=
    qz * qz - (Nat.card G : Subring.center (MonoidAlgebra ℂ G)) * qz
  let z : MonoidAlgebra ℂ G := zz.1
  have hzcenter : z ∈ Set.center (MonoidAlgebra ℂ G) := zz.property
  have hz_expand : z = q * q - (Nat.card G : ℂ) • q := by
    simp [z, zz, qz, Algebra.smul_def]
  have haction (j : d.I) {n : ℕ}
      (rho : Representation ℂ G (Fin n → ℂ))
      (hrho : d.chi j = rho.characterClassFunction) :
      rho.asAlgebraHom z =
        (0 : ℂ) • (1 : Module.End ℂ (Fin n → ℂ)) := by
    rw [hz_expand, map_sub, map_mul, map_smul]
    rw [complexCharacterProjectorNumerator_action d i j rho hrho]
    by_cases hij : i = j
    · simp [q, hij]
    · simp [q, hij]
  have hzcoeff (g : G) : z.coeff g = 0 := by
    have hcoeff :=
      BlockOrthogonality.coeff_eq_inv_card_mul_sum_scalar_degree_character
        d.chi d.complete z (Semigroup.mem_center_iff.mp hzcenter)
        (fun _ ↦ (0 : ℂ)) (by
          intro j n rho hrho
          exact haction j rho hrho) g
    simpa using hcoeff
  have hzzero : z = 0 := by
    ext g
    exact hzcoeff g
  rw [hz_expand] at hzzero
  exact sub_eq_zero.mp hzzero

/-- The integral numerator projector already satisfies `q² = |G| q` in
the localized cyclotomic group algebra. -/
theorem characterProjectorNumerator_mul_self
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    characterProjectorNumerator d i * characterProjectorNumerator d i =
      (Nat.card G : Localization.AtPrime d.primeIdeal) •
        characterProjectorNumerator d i := by
  classical
  apply mapRingHom_injective (localizationToComplex d)
    (localizationToComplex_injective d)
  rw [map_mul, map_characterProjectorNumerator,
    complexCharacterProjectorNumerator_mul_self]
  ext g
  simp [MonoidAlgebra.mapRingHom_apply]

end CharacterProjector

/-- Left multiplication by an arbitrary group-algebra element on the right
ideal generated by `q`. -/
def rightIdealLeftMul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (q a : MonoidAlgebra R G) :
    CentralIdempotentSupport.rightIdeal R q →ₗ[R]
      CentralIdempotentSupport.rightIdeal R q :=
  (LinearMap.mulLeft R a).restrict (by
    rintro _ ⟨x, rfl⟩
    refine ⟨a * x, ?_⟩
    exact mul_assoc _ _ _)

@[simp] theorem rightIdealLeftMul_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (q a : MonoidAlgebra R G)
    (x : CentralIdempotentSupport.rightIdeal R q) :
    (rightIdealLeftMul q a x : MonoidAlgebra R G) =
      a * (x : MonoidAlgebra R G) :=
  rfl

/-- The right ideal generated by any element of a finite group algebra over
a PID is finite free. -/
theorem rightIdeal_free
    {R : Type u} {G : Type v}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Group G] [Finite G]
    (q : MonoidAlgebra R G) :
    Module.Free R (CentralIdempotentSupport.rightIdeal R q) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module.Free R (MonoidAlgebra R G) := by infer_instance
  letI : Module.Finite R (MonoidAlgebra R G) := by infer_instance
  letI : Module.Finite R (CentralIdempotentSupport.rightIdeal R q) :=
    Module.Finite.range (LinearMap.mulRight R q)
  exact Module.free_of_finite_type_torsion_free'

/-- A scaled idempotence relation `q² = c q` says that right multiplication
by `q` acts by the scalar `c` on its own range. -/
theorem mulRight_restrict_range_eq_smul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (q : MonoidAlgebra R G) (c : R)
    (hq : q * q = c • q) :
    (LinearMap.mulRight R q).restrict
        (p := CentralIdempotentSupport.rightIdeal R q)
        (q := CentralIdempotentSupport.rightIdeal R q) (by
          rintro _ ⟨x, rfl⟩
          exact ⟨x * q, rfl⟩) =
      c • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  rcases hx with ⟨y, rfl⟩
  change (y * q) * q = c • (y * q)
  rw [mul_assoc, hq]
  exact Algebra.mul_smul_comm c y q

/-- The trace of `x ↦ a * x * q` on the ambient regular module is the
scaled trace of left multiplication by `a` on the right ideal generated by
`q`, provided `q² = c q`. -/
theorem trace_mulLeft_comp_mulRight_eq_smul_trace_rightIdeal
    {R : Type u} {G : Type v}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Group G] [Finite G]
    (q a : MonoidAlgebra R G) (c : R)
    (hq : q * q = c • q) :
    LinearMap.trace R (MonoidAlgebra R G)
        ((LinearMap.mulLeft R a).comp (LinearMap.mulRight R q)) =
      c * LinearMap.trace R
        (CentralIdempotentSupport.rightIdeal R q)
        (rightIdealLeftMul q a) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module.Free R (MonoidAlgebra R G) := by infer_instance
  letI : Module.Finite R (MonoidAlgebra R G) := by infer_instance
  let L := CentralIdempotentSupport.rightIdeal R q
  let F : Module.End R (MonoidAlgebra R G) :=
    (LinearMap.mulLeft R a).comp (LinearMap.mulRight R q)
  have hF (x : MonoidAlgebra R G) : F x ∈ L := by
    refine ⟨a * x, ?_⟩
    simp only [F, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]
    exact mul_assoc _ _ _
  have htrace := LinearMap.trace_restrict_eq_of_forall_mem L F hF
  rw [← htrace]
  have hrestrict : F.restrict (fun x hx ↦ hF x) =
      c • rightIdealLeftMul q a := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    rcases hx with ⟨y, rfl⟩
    change a * ((y * q) * q) = c • (a * (y * q))
    rw [mul_assoc, hq]
    rw [mul_smul_comm, mul_smul_comm]
  rw [hrestrict, map_smul]
  rfl

/-- General two-sided regular trace formula when the right factor is
central. -/
theorem trace_mulLeft_comp_mulRight_eq_card_mul_coeff_one
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (q a : MonoidAlgebra R G)
    (hq : q ∈ Set.center (MonoidAlgebra R G)) :
    LinearMap.trace R (MonoidAlgebra R G)
        ((LinearMap.mulLeft R a).comp (LinearMap.mulRight R q)) =
      (Nat.card G : R) * (a * q).coeff 1 := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      change LinearMap.trace R (MonoidAlgebra R G)
          ((LinearMap.mulLeft R (a + b)).comp (LinearMap.mulRight R q)) =
        (Nat.card G : R) * ((a + b) * q).coeff 1
      have hleft : LinearMap.mulLeft R (a + b) =
          LinearMap.mulLeft R a + LinearMap.mulLeft R b := by
        ext x
        simp
      rw [hleft, LinearMap.add_comp, map_add, ha, hb, add_mul]
      change (Nat.card G : R) * (a * q).coeff 1 +
          (Nat.card G : R) * (b * q).coeff 1 =
        (Nat.card G : R) * ((a * q).coeff 1 + (b * q).coeff 1)
      ring
  | single g r =>
      have hcomp :
          (LinearMap.mulLeft R
              (MonoidAlgebra.single g r : MonoidAlgebra R G)).comp
              (LinearMap.mulRight R q) =
            r • ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
              (LinearMap.mulRight R q)) := by
        ext x
        simp [MonoidAlgebra.of, LinearMap.comp_apply,
          Algebra.smul_mul_assoc]
      rw [hcomp, map_smul,
        CentralIdempotentSupport.trace_mulLeft_comp_mulRight q hq g]
      rw [smul_eq_mul]
      change r * ((Nat.card G : R) * q g⁻¹) =
        (Nat.card G : R) * (MonoidAlgebra.single g r * q) 1
      rw [MonoidAlgebra.single_mul_apply]
      simp
      ring

/-- On a denominator-cleared isotypic right ideal, the trace of left
multiplication is the identity coefficient of `a * q`.  The two factors of
`|G|` in the ambient regular trace cancel. -/
theorem trace_rightIdealLeftMul_eq_coeff_one
    {R : Type u} {G : Type v}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Group G] [Finite G]
    (q a : MonoidAlgebra R G)
    (hqcenter : q ∈ Set.center (MonoidAlgebra R G))
    (hq : q * q = (Nat.card G : R) • q)
    (hcard : (Nat.card G : R) ≠ 0) :
    LinearMap.trace R
        (CentralIdempotentSupport.rightIdeal R q)
        (rightIdealLeftMul q a) =
      (a * q).coeff 1 := by
  apply mul_left_cancel₀ hcard
  calc
    (Nat.card G : R) *
          LinearMap.trace R
            (CentralIdempotentSupport.rightIdeal R q)
            (rightIdealLeftMul q a) =
        LinearMap.trace R (MonoidAlgebra R G)
          ((LinearMap.mulLeft R a).comp (LinearMap.mulRight R q)) :=
      (trace_mulLeft_comp_mulRight_eq_smul_trace_rightIdeal
        q a (Nat.card G : R) hq).symm
    _ = (Nat.card G : R) * (a * q).coeff 1 :=
      trace_mulLeft_comp_mulRight_eq_card_mul_coeff_one q a hqcenter

end IsotypicLattice
end Submission.ZStar
