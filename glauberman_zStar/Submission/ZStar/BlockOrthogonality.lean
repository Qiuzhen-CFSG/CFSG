import Submission.ZStar.PrincipalBlockConstruction
import Submission.ZStar.CentralIdempotentSupport
import Submission.BenderSuzuki.External.Suzuki.VI.formula_1_7
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Weak block orthogonality

This file develops the group-algebra form of Feit IV.7.2.  The coefficient
of an element `g` in a block central idempotent is

`|G|⁻¹ * ∑ χ in B, χ(1) χ(g⁻¹)`.

Thus the weak orthogonality relation needed in the `Z*` argument follows
once the integral block idempotent is known to have zero coefficient on
`2`-singular elements.  The lemmas below isolate the character-theoretic
coefficient calculation from that local integral-algebra input.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace BlockOrthogonality

open BlockPreliminaries PrincipalBlockConstruction

attribute [local instance] Fintype.ofFinite

universe u v w

/-- The elements of a conjugacy class as a finite set. -/
private noncomputable def classSet
    {G : Type u} [Group G] [Finite G] (c : ConjClasses G) : Finset G :=
  letI : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)
  Finset.univ.filter fun g : G => ConjClasses.mk g = c

private theorem mem_classSet_iff
    {G : Type u} [Group G] [Finite G]
    {c : ConjClasses G} {g : G} :
    g ∈ classSet c ↔ ConjClasses.mk g = c := by
  classical
  simp [classSet]

private theorem classSet_card
    {G : Type u} [Group G] [Finite G]
    (c : ConjClasses G) :
    (classSet c).card = Nat.card c.carrier := by
  classical
  let e : {g : G // g ∈ classSet c} ≃ c.carrier :=
    { toFun := fun x =>
        ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr
          (mem_classSet_iff.mp x.2)⟩
      invFun := fun x =>
        ⟨x, mem_classSet_iff.mpr
          (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr e

/-- The sum of the elements in a conjugacy class, over an arbitrary
coefficient ring. -/
private noncomputable def classSum
    {G : Type u} [Group G] [Finite G]
    (R : Type v) [CommRing R] (c : ConjClasses G) : MonoidAlgebra R G :=
  ∑ g ∈ classSet c, MonoidAlgebra.single g 1

private theorem classSum_coeff
    {G : Type u} [Group G] [Finite G] [DecidableEq (ConjClasses G)]
    (R : Type v) [CommRing R] (c : ConjClasses G) (g : G) :
    (classSum R c).coeff g = if ConjClasses.mk g = c then 1 else 0 := by
  classical
  rw [classSum]
  simp only [MonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  change ∑ x ∈ classSet c, (Finsupp.single x (1 : R)) g = _
  by_cases hgc : ConjClasses.mk g = c
  · rw [if_pos hgc]
    have hgmem : g ∈ classSet c := mem_classSet_iff.mpr hgc
    rw [Finset.sum_eq_single g]
    · simp
    · intro x _hx hxg
      simp [hxg]
    · intro hgnot
      exact (hgnot hgmem).elim
  · rw [if_neg hgc]
    apply Finset.sum_eq_zero
    intro x _hx
    have hxg : x ≠ g := by
      intro hxg
      apply hgc
      simpa [hxg] using (mem_classSet_iff.mp _hx)
    simp [hxg]

private theorem classSum_apply
    {G : Type u} [Group G] [Finite G] [DecidableEq (ConjClasses G)]
    (R : Type v) [CommRing R] (c : ConjClasses G) (g : G) :
    classSum R c g = if ConjClasses.mk g = c then 1 else 0 :=
  classSum_coeff R c g

private theorem classSum_single_comm
    {G : Type u} [Group G] [Finite G]
    (R : Type v) [CommRing R] (c : ConjClasses G) (h : G) :
    (MonoidAlgebra.single h 1 : MonoidAlgebra R G) * classSum R c =
      classSum R c * MonoidAlgebra.single h 1 := by
  classical
  ext x
  simp only [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply,
    one_mul, mul_one, classSum_apply]
  have hconj :
      ConjClasses.mk (h⁻¹ * x) = ConjClasses.mk (x * h⁻¹) := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    exact ⟨h, by group⟩
  rw [hconj]

private theorem classSum_comm
    {G : Type u} [Group G] [Finite G]
    (R : Type v) [CommRing R] (c : ConjClasses G)
    (a : MonoidAlgebra R G) :
    a * classSum R c = classSum R c * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      have hconj :
          ConjClasses.mk (g⁻¹ * x) = ConjClasses.mk (x * g⁻¹) := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨g, by group⟩
      simp only [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply,
        classSum_apply]
      rw [hconj, mul_comm]

/-- Changing coefficients in a conjugacy-class sum simply changes every
coefficient `1`. -/
private theorem mapRingHom_classSum
    {G : Type u} [Group G] [Finite G]
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (c : ConjClasses G) :
    MonoidAlgebra.mapRingHom G f (classSum R c) = classSum S c := by
  classical
  simp [classSum]

private theorem single_one_mul_eq_smul
    {G : Type u} [Group G]
    {R : Type v} [CommRing R]
    (r : R) (a : MonoidAlgebra R G) :
    MonoidAlgebra.single 1 r * a = r • a := by
  ext g
  simp [MonoidAlgebra.single_mul_apply]

private theorem smul_sub_smul_eq
    {M : Type v} [AddCommGroup M] [Module ℂ M]
    (a b c : ℂ) (x : M) :
    a • (b • x - c • x) = (a * (b - c)) • x := by
  calc
    a • (b • x - c • x) = a • ((b - c) • x) := by
      exact congrArg (fun y : M => a • y) (sub_smul b c x).symm
    _ = (a * (b - c)) • x := smul_smul a (b - c) x

private noncomputable def centralIntertwiner
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    Representation.IntertwiningMap ρ ρ where
  toLinearMap := ρ.asAlgebraHom z
  isIntertwining' g := by
    rw [← Representation.asAlgebraHom_single_one (ρ := ρ) g]
    change ρ.asAlgebraHom z *
        ρ.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) =
      ρ.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) * ρ.asAlgebraHom z
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.asAlgebraHom (hz (MonoidAlgebra.single g (1 : ℂ))).symm

private lemma centralIntertwiner_eq_scalar
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (z : MonoidAlgebra ℂ G) (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    ∃ a : ℂ, ρ.asAlgebraHom z = a • (1 : Module.End ℂ V) := by
  classical
  have hfin :
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 :=
    (Representation.irreducible_iff_end_dimension_one (ρ := ρ)).1 inferInstance
  haveI : Nontrivial V := Representation.irreducible_nontrivial (ρ := ρ)
  have hone_ne_zero :
      (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvzero : v = 0 := by
      simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
    exact hv hvzero
  obtain ⟨a, ha⟩ :
      ∃ a : ℂ, a • (1 : Representation.IntertwiningMap ρ ρ) =
        centralIntertwiner ρ z hz :=
    (finrank_eq_one_iff_of_nonzero'
      (K := ℂ) (V := Representation.IntertwiningMap ρ ρ)
      (1 : Representation.IntertwiningMap ρ ρ) hone_ne_zero).mp hfin
      (centralIntertwiner ρ z hz)
  refine ⟨a, ?_⟩
  ext v
  simpa [centralIntertwiner] using
    (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) ha).symm

private theorem classSum_trace
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (c : ConjClasses G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
      ∑ g ∈ classSet c, ρ.character g := by
  classical
  simp [classSum, Representation.character, map_sum]

private theorem classSum_action_eq_centralCharacter
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    ∃ a : ℂ,
      ρ.asAlgebraHom (classSum ℂ c) = a • (1 : Module.End ℂ V) ∧
      a = ordinaryCentralCharacterValue ρ.characterClassFunction
        (c := c) := by
  classical
  letI : Nontrivial V := Representation.irreducible_nontrivial (ρ := ρ)
  obtain ⟨a, ha⟩ := centralIntertwiner_eq_scalar ρ (classSum ℂ c)
    (classSum_comm ℂ c)
  have htrace₁ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        ∑ g ∈ classSet c, ρ.character g := classSum_trace ρ c
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep c
  have hxc : x ∈ c.carrier :=
    ConjClasses.mem_carrier_iff_mk_eq.mpr hx
  have hconst : ∀ g ∈ classSet c, ρ.character g = ρ.character x := by
    intro g hg
    change ρ.characterClassFunction (ConjClasses.mk g) =
      ρ.characterClassFunction (ConjClasses.mk x)
    rw [mem_classSet_iff.mp hg, hx]
  have htrace₁' :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        (Nat.card c.carrier : ℂ) * ρ.character x := by
    rw [htrace₁]
    calc
      (∑ g ∈ classSet c, ρ.character g) =
          ∑ _g ∈ classSet c, ρ.character x := by
            apply Finset.sum_congr rfl
            intro g hg
            exact hconst g hg
      _ = (Nat.card c.carrier : ℂ) * ρ.character x := by
            rw [Finset.sum_const, classSet_card]
            simp [nsmul_eq_mul]
  have htrace₂ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        a * (Module.finrank ℂ V : ℂ) := by
    rw [ha, map_smul]
    simp
  have hdegree : ρ.character 1 = (Module.finrank ℂ V : ℂ) := by
    simp [Representation.character]
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ V :=
      (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
    exact_mod_cast hpos.ne'
  refine ⟨a, ha, ?_⟩
  rw [ordinaryCentralCharacterValue]
  have hχc : ρ.characterClassFunction c = ρ.character x := by
    rw [← hx]
    rfl
  have hχone :
      ρ.characterClassFunction (ConjClasses.mk (1 : G)) = ρ.character 1 := rfl
  rw [hχc, hχone]
  rw [hdegree]
  have hscalar :
      a * (Module.finrank ℂ V : ℂ) =
        (Nat.card c.carrier : ℂ) * ρ.character x :=
    htrace₂.symm.trans htrace₁'
  field_simp [hdim_ne]
  simpa [mul_comm] using hscalar

/-- A central group-algebra element gives a class function by taking the
coefficient of the inverse element. -/
private noncomputable def coeffInvClassFunction
    {G : Type u} [Group G] [Finite G]
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    Representation.ClassFunction G :=
  Representation.classFunctionOfInvariant (fun g : G => z g⁻¹) (by
    intro g h
    have heq := congrArg (fun q : MonoidAlgebra ℂ G => q (h * g⁻¹))
      (hz (MonoidAlgebra.single h (1 : ℂ)))
    simpa [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply,
      mul_assoc] using heq.symm)

@[simp] private theorem coeffInvClassFunction_mk
    {G : Type u} [Group G] [Finite G]
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a)
    (g : G) :
    coeffInvClassFunction z hz (ConjClasses.mk g) = z g⁻¹ := rfl

private theorem groupAlgebra_trace
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (z : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom z) =
      ∑ g : G, z.coeff g * ρ.character g := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      change (∑ g : G, x.coeff g * ρ.character g) +
          (∑ g : G, y.coeff g * ρ.character g) =
        ∑ g : G, (x.coeff g + y.coeff g) * ρ.character g
      simp only [add_mul, Finset.sum_add_distrib]
  | single g r =>
      have hmap :
          ρ.asAlgebraHom (MonoidAlgebra.single g r) = r • ρ g := by
        rw [show (MonoidAlgebra.single g r : MonoidAlgebra ℂ G) =
          r • MonoidAlgebra.single g 1 by simp, map_smul,
          Representation.asAlgebraHom_single_one]
      rw [hmap, map_smul]
      change r * ρ.character g =
        ∑ x : G, (MonoidAlgebra.single g r).coeff x * ρ.character x
      rw [Finset.sum_eq_single g]
      · change r * ρ.character g = (Finsupp.single g r) g * ρ.character g
        simp
      · intro x _hx hxg
        change (Finsupp.single g r) x * ρ.character x = 0
        simp [hxg]
      · simp

private theorem inner_coeffInv_eq
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a)
    (lambda : ℂ)
    (haction : ρ.asAlgebraHom z = lambda • (1 : Module.End ℂ V)) :
    Representation.classFunctionInner (coeffInvClassFunction z hz)
        ρ.characterClassFunction =
      (Nat.card G : ℂ)⁻¹ *
        (lambda * ρ.character 1) := by
  classical
  have hinvsum :
      (∑ g : G, z g⁻¹ * star (ρ.character g)) =
        ∑ g : G, z.coeff g * ρ.character g := by
    let f : G → ℂ := fun g => z.coeff g * ρ.character g
    calc
      (∑ g : G, z.coeff g⁻¹ * star (ρ.character g)) =
          ∑ g : G, f g⁻¹ := by
            apply Finset.sum_congr rfl
            intro g _hg
            simp only [f]
            rw [Representation.representation_character_inv_eq_star_character]
      _ = ∑ g : G, f g := Equiv.sum_comp (Equiv.inv G) f
      _ = ∑ g : G, z.coeff g * ρ.character g := rfl
  rw [Representation.classFunctionInner]
  change (Nat.card G : ℂ)⁻¹ *
      (∑ g : G, z g⁻¹ * star (ρ.character g)) = _
  rw [hinvsum, ← groupAlgebra_trace ρ z, haction, map_smul]
  simp [Representation.character]

/-- Recover the coefficient of a central group-algebra element from the
scalars by which it acts on a complete family of irreducibles.  This is the
abstract coefficient formula behind Feit IV.7.1. -/
theorem coeff_eq_inv_card_mul_sum_scalar_degree_character
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → Representation.ClassFunction G)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a)
    (lambda : I → ℂ)
    (haction : ∀ i : I, ∀ {n : ℕ}
      (ρ : Representation ℂ G (Fin n → ℂ)),
      chi i = ρ.characterClassFunction →
      ρ.asAlgebraHom z = lambda i • (1 : Module.End ℂ (Fin n → ℂ)))
    (g : G) :
    z.coeff g = (Nat.card G : ℂ)⁻¹ *
      ∑ i : I, lambda i * chi i (ConjClasses.mk (1 : G)) *
        chi i (ConjClasses.mk g⁻¹) := by
  classical
  let phi : Representation.ClassFunction G := coeffInvClassFunction z hz
  have hinner (i : I) :
      Representation.classFunctionInner phi (chi i) =
        (Nat.card G : ℂ)⁻¹ *
          (lambda i * chi i (ConjClasses.mk (1 : G))) := by
    rcases (hchi.1 i).1 with ⟨n, ρ, hρ⟩
    rw [hρ]
    exact inner_coeffInv_eq ρ z hz (lambda i) (haction i ρ hρ)
  have hexpand :=
    Representation.completeFamily_apply_eq_sum_inner hchi phi
      (ConjClasses.mk g⁻¹)
  change z.coeff (g⁻¹)⁻¹ =
      ∑ i : I, Representation.classFunctionInner phi (chi i) *
        chi i (ConjClasses.mk g⁻¹) at hexpand
  rw [inv_inv] at hexpand
  rw [hexpand]
  simp_rw [hinner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

section LocalBlockElement

variable {G : Type u} [Group G] [Finite G]

private abbrev cyclotomicOrderAtPrime
    {eta : ℂ} (P : Ideal (Representation.cyclotomicOrder eta))
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P

private noncomputable def localizationToComplex
    {eta : ℂ} (P : Ideal (Representation.cyclotomicOrder eta))
    [P.IsPrime] :
    cyclotomicOrderAtPrime P →+* ℂ := by
  let A := Representation.cyclotomicOrder eta
  let f : A →+* ℂ := Subring.subtype A
  exact IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := f) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro hy
      apply y.2
      have hyA : (y.1 : ℂ) = 0 := by
        simpa [f] using hy
      have hyzero : y.1 = 0 := Subtype.ext hyA
      rw [hyzero]
      exact P.zero_mem)

private theorem localizationToComplex_algebraMap
    {eta : ℂ} (P : Ideal (Representation.cyclotomicOrder eta))
    [P.IsPrime] (a : Representation.cyclotomicOrder eta) :
    localizationToComplex P (algebraMap _ _ a) = (a : ℂ) := by
  apply IsLocalization.lift_eq

end LocalBlockElement

section BlockIndicator

variable {G : Type u} [Group G] [Finite G]

private instance principalPrimeIdeal_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

private theorem exists_separating_class
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    ∃ c : ConjClasses G,
      centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) c -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) c ∉ d.primeIdeal := by
  classical
  have hij : ¬ SameTwoBlock d.eta_spec d.primeIdeal
      (d.chi i) (d.chi j) (d.complete.1 i) (d.complete.1 j) := by
    intro h
    apply hj
    apply (d.mem_block_iff j).2
    exact sameTwoBlock_trans d.eta_spec d.primeIdeal
      (sameTwoBlock_symm d.eta_spec d.primeIdeal
        h)
      ((d.mem_block_iff i).1 hi)
  by_contra hsep
  apply hij
  apply (sameTwoBlock_iff d.eta_spec d.primeIdeal
    (d.chi i) (d.chi j) (d.complete.1 i) (d.complete.1 j)).2
  intro c
  by_contra hc
  exact hsep ⟨c, hc⟩

private noncomputable def separatingClass
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) : ConjClasses G :=
  Classical.choose (exists_separating_class d hi hj)

private theorem separatingClass_spec
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) ∉ d.primeIdeal :=
  Classical.choose_spec (exists_separating_class d hi hj)

private noncomputable def localizedCentralCharacter
    (d : PrincipalCongruenceBlockData G) (i : d.I) (c : ConjClasses G) :
    cyclotomicOrderAtPrime d.primeIdeal :=
  algebraMap _ _ (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
    (d.complete.1 i) c)

private theorem localizationToComplex_localizedCentralCharacter
    (d : PrincipalCongruenceBlockData G) (i : d.I) (c : ConjClasses G) :
    localizationToComplex d.primeIdeal (localizedCentralCharacter d i c) =
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
        (d.complete.1 i) c : ℂ) := by
  exact localizationToComplex_algebraMap d.primeIdeal _

private noncomputable def denominatorInverse
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    cyclotomicOrderAtPrime d.primeIdeal := by
  let a := centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
      (d.complete.1 i) (separatingClass d hi hj) -
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
      (d.complete.1 j) (separatingClass d hi hj)
  let hmem : a ∈ d.primeIdeal.primeCompl :=
    show a ∉ d.primeIdeal from separatingClass_spec d hi hj
  exact IsLocalization.mk' (Localization.AtPrime d.primeIdeal) 1 ⟨a, hmem⟩

private theorem denominatorInverse_map
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    localizationToComplex d.primeIdeal
        (denominatorInverse d hi hj) =
      ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹ := by
  classical
  let A := Representation.cyclotomicOrder d.eta
  let a := centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
      (d.complete.1 i) (separatingClass d hi hj) -
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
      (d.complete.1 j) (separatingClass d hi hj)
  let hmem : a ∈ d.primeIdeal.primeCompl :=
    separatingClass_spec d hi hj
  simp only [denominatorInverse]
  rw [show localizationToComplex d.primeIdeal =
      IsLocalization.lift (M := d.primeIdeal.primeCompl)
        (S := Localization.AtPrime d.primeIdeal)
        (g := Subring.subtype (Representation.cyclotomicOrder d.eta))
        (by
          intro y
          apply isUnit_iff_ne_zero.mpr
          intro hy
          apply y.2
          have hyA : (y.1 : ℂ) = 0 := hy
          have hyzero : y.1 = 0 := Subtype.ext hyA
          rw [hyzero]
          exact d.primeIdeal.zero_mem) by rfl]
  rw [IsLocalization.lift_mk']
  simp [IsUnit.coe_liftRight]

private noncomputable def localizedGroupAlgebraToComplex
    (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G →+*
      MonoidAlgebra ℂ G :=
  MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)

/-- A localized class-sum polynomial which acts as `1` on `i` and as `0`
on `j`. -/
private noncomputable def separatingFactor
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G :=
  MonoidAlgebra.single 1 (denominatorInverse d hi hj) *
    (classSum (cyclotomicOrderAtPrime d.primeIdeal)
        (separatingClass d hi hj) -
      MonoidAlgebra.single 1
        (localizedCentralCharacter d j (separatingClass d hi hj)))

private theorem map_separatingFactor
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    localizedGroupAlgebraToComplex d (separatingFactor d hi hj) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d hi hj) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d hi hj) : ℂ) • 1) := by
  classical
  simp only [separatingFactor, localizedGroupAlgebraToComplex, map_mul,
    map_sub, MonoidAlgebra.mapRingHom_single, mapRingHom_classSum]
  rw [show localizationToComplex d.primeIdeal
      (denominatorInverse d hi hj) =
        ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹ by
      exact denominatorInverse_map d hi hj]
  have hsingle (r : ℂ) :
      (MonoidAlgebra.single 1 r : MonoidAlgebra ℂ G) = r • 1 := by
    simp [MonoidAlgebra.one_def]
  calc
    MonoidAlgebra.single 1
          (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
            (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
              (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
                (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) *
        (classSum ℂ (separatingClass d hi hj) -
          MonoidAlgebra.single 1
            (localizationToComplex d.primeIdeal
              (localizedCentralCharacter d j (separatingClass d hi hj)))) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d hi hj) -
          MonoidAlgebra.single 1
            (localizationToComplex d.primeIdeal
              (localizedCentralCharacter d j (separatingClass d hi hj)))) := by
      exact single_one_mul_eq_smul _ _
    _ = (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d hi hj) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d hi hj) : ℂ) • 1) := by
      rw [localizationToComplex_localizedCentralCharacter,
        hsingle]

private theorem separatingFactor_comm
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    (a : MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :
    a * separatingFactor d hi hj = separatingFactor d hi hj * a := by
  classical
  rw [separatingFactor]
  have hdenom :
      a * MonoidAlgebra.single 1 (denominatorInverse d hi hj) =
        MonoidAlgebra.single 1 (denominatorInverse d hi hj) * a := by
    ext x
    simp [mul_comm]
  let x := classSum (cyclotomicOrderAtPrime d.primeIdeal)
      (separatingClass d hi hj) -
    MonoidAlgebra.single 1
      (localizedCentralCharacter d j (separatingClass d hi hj))
  have hx : a * x = x * a := by
    have hclass : classSum (cyclotomicOrderAtPrime d.primeIdeal)
        (separatingClass d hi hj) ∈
        Set.center (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
      (Semigroup.mem_center_iff).2
        (classSum_comm (cyclotomicOrderAtPrime d.primeIdeal)
          (separatingClass d hi hj))
    have hscalar : MonoidAlgebra.single 1
        (localizedCentralCharacter d j (separatingClass d hi hj)) ∈
        Set.center (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) := by
      apply (Semigroup.mem_center_iff).2
      intro b
      ext g
      simp [mul_comm]
    have hxcenter : x ∈
        Set.center (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) := by
      dsimp only [x]
      rw [sub_eq_add_neg]
      exact Set.add_mem_center hclass (Set.neg_mem_center hscalar)
    exact (Semigroup.mem_center_iff.mp hxcenter) a
  calc
    a * (MonoidAlgebra.single 1 (denominatorInverse d hi hj) * x) =
        (a * MonoidAlgebra.single 1 (denominatorInverse d hi hj)) * x :=
      (mul_assoc _ _ _).symm
    _ = (MonoidAlgebra.single 1 (denominatorInverse d hi hj) * a) * x := by
      rw [hdenom]
    _ = MonoidAlgebra.single 1 (denominatorInverse d hi hj) * (a * x) :=
      mul_assoc _ _ _
    _ = MonoidAlgebra.single 1 (denominatorInverse d hi hj) * (x * a) := by
      rw [hx]
    _ = (MonoidAlgebra.single 1 (denominatorInverse d hi hj) * x) * a :=
      (mul_assoc _ _ _).symm

private theorem separatingDifference_ne_zero
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ) ≠ 0 := by
  intro hzero
  apply separatingClass_spec d hi hj
  have hzero' :
      centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hzero']
  exact d.primeIdeal.zero_mem

private theorem separatingFactor_action
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    (l : d.I) {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = ρ.characterClassFunction) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d hi hj)) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹ *
        ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi l)
          (d.complete.1 l) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  have hρirr : Representation.IsIrreducible ρ := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 l).2
  letI : Representation.IsIrreducible ρ := hρirr
  let c := separatingClass d hi hj
  obtain ⟨a, ha, haeq⟩ := classSum_action_eq_centralCharacter ρ c
  have hclass : ρ.asAlgebraHom (classSum ℂ c) =
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi l)
        (d.complete.1 l) c : ℂ) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
    calc
      ρ.asAlgebraHom (classSum ℂ c) =
          a • (1 : Module.End ℂ (Fin n → ℂ)) := ha
      _ = ordinaryCentralCharacterValue ρ.characterClassFunction c •
          (1 : Module.End ℂ (Fin n → ℂ)) := by rw [haeq]
      _ = (centralCharacterInCyclotomicOrder d.eta_spec (d.chi l)
            (d.complete.1 l) c : ℂ) •
          (1 : Module.End ℂ (Fin n → ℂ)) := by
        apply congrArg (fun z : ℂ =>
          z • (1 : Module.End ℂ (Fin n → ℂ)))
        change ordinaryCentralCharacterValue ρ.characterClassFunction c =
          ordinaryCentralCharacterValue (d.chi l) c
        exact congrArg (fun χ : Representation.ClassFunction G =>
          ordinaryCentralCharacterValue χ c) hρ.symm
  dsimp only [c] at hclass
  rw [map_separatingFactor]
  rw [map_smul, map_sub, map_smul, map_one, hclass]
  exact smul_sub_smul_eq _ _ _ _

private theorem separatingFactor_action_self
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i = ρ.characterClassFunction) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d hi hj)) = 1 := by
  rw [separatingFactor_action d hi hj i ρ hρ]
  rw [inv_mul_cancel₀ (separatingDifference_ne_zero d hi hj)]
  exact one_smul ℂ _

private theorem separatingFactor_action_other
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi j = ρ.characterClassFunction) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d hi hj)) = 0 := by
  rw [separatingFactor_action d hi hj j ρ hρ]
  simp

private abbrev blockCharacterIndex (d : PrincipalCongruenceBlockData G) :=
  {i : d.I // i ∈ d.block}

private abbrev outsideCharacterIndex (d : PrincipalCongruenceBlockData G) :=
  {j : d.I // j ∉ d.block}

private instance localizedCenterCommRing
    (d : PrincipalCongruenceBlockData G) :
    CommRing (Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) :=
  @Subring.instCommRingSubtypeMemCenter _
    (inferInstance : Ring
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G))

private noncomputable def separatingFactorCenter
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  ⟨separatingFactor d hi hj,
    (Semigroup.mem_center_iff).2 (separatingFactor_comm d hi hj)⟩

/-- A central localized element which acts as `1` on one prescribed block
character and as `0` on every character outside the block. -/
private noncomputable def characterSelector
    (d : PrincipalCongruenceBlockData G) (i : blockCharacterIndex d) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  ∏ j : outsideCharacterIndex d,
    separatingFactorCenter d i.property j.property

private theorem characterSelector_action_self
    (d : PrincipalCongruenceBlockData G) (i : blockCharacterIndex d)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i.1 = ρ.characterClassFunction) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (characterSelector d i :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 1 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  change Φ (characterSelector d i) = 1
  have hprod (s : Finset (outsideCharacterIndex d)) :
      Φ (∏ j ∈ s, separatingFactorCenter d i.property j.property) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, map_mul, ih, mul_one]
        change ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
          (separatingFactor d i.property j.property)) = 1
        exact separatingFactor_action_self d i.property j.property ρ hρ
  simpa only [characterSelector] using hprod Finset.univ

private theorem characterSelector_action_outside
    (d : PrincipalCongruenceBlockData G) (i : blockCharacterIndex d)
    (l : d.I) (hl : l ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = ρ.characterClassFunction) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (characterSelector d i :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 0 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  let j₀ : outsideCharacterIndex d := ⟨l, hl⟩
  change Φ (characterSelector d i) = 0
  rw [characterSelector]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j : outsideCharacterIndex d =>
      separatingFactorCenter d i.property j.property)
    (Finset.mem_univ j₀)]
  rw [map_mul]
  have hzero : Φ (separatingFactorCenter d i.property j₀.property) = 0 := by
    change ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
      (separatingFactor d i.property hl)) = 0
    exact separatingFactor_action_other d i.property hl ρ hρ
  rw [hzero, zero_mul]

/-- The localized central element whose irreducible scalars are the
characteristic function of the principal congruence block. -/
private noncomputable def localizedBlockIndicatorCenter
    (d : PrincipalCongruenceBlockData G) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  1 - ∏ i : blockCharacterIndex d, (1 - characterSelector d i)

private theorem localizedBlockIndicator_action_mem
    (d : PrincipalCongruenceBlockData G) (l : d.I) (hl : l ∈ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = ρ.characterClassFunction) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (localizedBlockIndicatorCenter d :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 1 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  let i₀ : blockCharacterIndex d := ⟨l, hl⟩
  change Φ (localizedBlockIndicatorCenter d) = 1
  rw [localizedBlockIndicatorCenter, map_sub, map_one]
  have hfactor : Φ (1 - characterSelector d i₀) = 0 := by
    rw [map_sub, map_one]
    change 1 - ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
      (characterSelector d i₀ : A)) = 0
    rw [characterSelector_action_self d i₀ ρ hρ]
    exact sub_self 1
  have hproduct :
      Φ (∏ i : blockCharacterIndex d, (1 - characterSelector d i)) = 0 := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i : blockCharacterIndex d => 1 - characterSelector d i)
      (Finset.mem_univ i₀)]
    rw [map_mul, hfactor, zero_mul]
  rw [hproduct, sub_zero]

private theorem localizedBlockIndicator_action_not_mem
    (d : PrincipalCongruenceBlockData G) (l : d.I) (hl : l ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = ρ.characterClassFunction) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (localizedBlockIndicatorCenter d :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 0 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  change Φ (localizedBlockIndicatorCenter d) = 0
  rw [localizedBlockIndicatorCenter, map_sub, map_one]
  have hprod (s : Finset (blockCharacterIndex d)) :
      Φ (∏ i ∈ s, (1 - characterSelector d i)) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, map_mul, ih, mul_one]
        rw [map_sub, map_one]
        change 1 - ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
          (characterSelector d i : A)) = 1
        rw [characterSelector_action_outside d i l hl ρ hρ]
        exact sub_zero 1
  rw [hprod Finset.univ, sub_self]

/-- The integral-localized principal-block element. -/
noncomputable def localizedPrincipalBlockElement
    (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G :=
  localizedBlockIndicatorCenter d

/-- The complex principal-block central element obtained by extending
coefficients from the localized cyclotomic order. -/
noncomputable def principalBlockElement
    (d : PrincipalCongruenceBlockData G) : MonoidAlgebra ℂ G :=
  localizedGroupAlgebraToComplex d (localizedPrincipalBlockElement d)

/-- The complex principal-block element is independent of the presentation of
the canonical localization lift.  This lets downstream arguments use their
own named copy of the localization-to-`ℂ` homomorphism. -/
theorem mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
    (d : PrincipalCongruenceBlockData G)
    (f : cyclotomicOrderAtPrime d.primeIdeal →+* ℂ)
    (hf : ∀ a : Representation.cyclotomicOrder d.eta,
      f (algebraMap _ (cyclotomicOrderAtPrime d.primeIdeal) a) = (a : ℂ)) :
    MonoidAlgebra.mapRingHom G f (localizedPrincipalBlockElement d) =
      principalBlockElement d := by
  change MonoidAlgebra.mapRingHom G f (localizedPrincipalBlockElement d) =
    MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
      (localizedPrincipalBlockElement d)
  have hfg : f = localizationToComplex d.primeIdeal := by
    apply IsLocalization.ringHom_ext d.primeIdeal.primeCompl
    apply RingHom.ext
    intro a
    change f (algebraMap _ (cyclotomicOrderAtPrime d.primeIdeal) a) =
      localizationToComplex d.primeIdeal
        (algebraMap _ (cyclotomicOrderAtPrime d.primeIdeal) a)
    rw [hf, localizationToComplex_algebraMap]
  rw [hfg]

theorem principalBlockElement_action
    (d : PrincipalCongruenceBlockData G) (l : d.I)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = ρ.characterClassFunction) :
    ρ.asAlgebraHom (principalBlockElement d) =
      (if l ∈ d.block then (1 : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  by_cases hl : l ∈ d.block
  · rw [if_pos hl, one_smul]
    exact localizedBlockIndicator_action_mem d l hl ρ hρ
  · rw [if_neg hl, zero_smul]
    exact localizedBlockIndicator_action_not_mem d l hl ρ hρ

private theorem map_localized_center_comm
    (d : PrincipalCongruenceBlockData G)
    (z : Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G))
    (a : MonoidAlgebra ℂ G) :
    a * localizedGroupAlgebraToComplex d
          (z : MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) =
      localizedGroupAlgebraToComplex d
          (z : MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      have hz := (Semigroup.mem_center_iff.mp z.property)
        (MonoidAlgebra.single g
          (1 : cyclotomicOrderAtPrime d.primeIdeal))
      have hzmap := congrArg (localizedGroupAlgebraToComplex d) hz
      have hzmap' :
          (MonoidAlgebra.single g (1 : ℂ)) *
              localizedGroupAlgebraToComplex d
                (z : MonoidAlgebra
                  (cyclotomicOrderAtPrime d.primeIdeal) G) =
            localizedGroupAlgebraToComplex d
                (z : MonoidAlgebra
                  (cyclotomicOrderAtPrime d.primeIdeal) G) *
              MonoidAlgebra.single g (1 : ℂ) := by
        simpa [localizedGroupAlgebraToComplex] using hzmap
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra ℂ G) =
        r • MonoidAlgebra.single g 1 by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      rw [hzmap']

theorem localizedPrincipalBlockElement_mem_center
    (d : PrincipalCongruenceBlockData G) :
    localizedPrincipalBlockElement d ∈
      Set.center
        (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  (localizedBlockIndicatorCenter d).property

theorem principalBlockElement_comm
    (d : PrincipalCongruenceBlockData G) (a : MonoidAlgebra ℂ G) :
    a * principalBlockElement d = principalBlockElement d * a :=
  map_localized_center_comm d (localizedBlockIndicatorCenter d) a

theorem principalBlockElement_mem_center
    (d : PrincipalCongruenceBlockData G) :
    principalBlockElement d ∈ Set.center (MonoidAlgebra ℂ G) :=
  (Semigroup.mem_center_iff).2 (principalBlockElement_comm d)

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
      d.chi i = ρ.characterClassFunction →
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

private theorem localizationToComplex_injective
    (d : PrincipalCongruenceBlockData G) :
    Function.Injective (localizationToComplex d.primeIdeal) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    d.primeIdeal.primeCompl (localizationToComplex d.primeIdeal)).2
  intro x y
  constructor
  · intro h
    exact congrArg (localizationToComplex d.primeIdeal) h
  · intro h
    have hcoe : (x : ℂ) = (y : ℂ) := by
      simpa only [localizationToComplex_algebraMap] using h
    have hxy : x = y := Subtype.ext hcoe
    rw [hxy]

private instance cyclotomicOrderAtPrime_charZero
    (d : PrincipalCongruenceBlockData G) :
    CharZero (cyclotomicOrderAtPrime d.primeIdeal) where
  cast_injective m n hmn := by
    apply CharZero.cast_injective (R := ℂ)
    have hmap := congrArg (localizationToComplex d.primeIdeal) hmn
    simpa using hmap

theorem two_not_isUnit_cyclotomicOrderAtPrime
    (d : PrincipalCongruenceBlockData G) :
    ¬ IsUnit (2 : cyclotomicOrderAtPrime d.primeIdeal) := by
  intro hunit
  have hunit' : IsUnit
      (algebraMap (Representation.cyclotomicOrder d.eta)
        (cyclotomicOrderAtPrime d.primeIdeal)
        (2 : Representation.cyclotomicOrder d.eta)) := by
    simpa only [map_ofNat] using hunit
  rw [← IsLocalization.mk'_one
    (M := d.primeIdeal.primeCompl)
    (cyclotomicOrderAtPrime d.primeIdeal)
      (2 : Representation.cyclotomicOrder d.eta),
    IsLocalization.AtPrime.isUnit_mk'_iff
      (cyclotomicOrderAtPrime d.primeIdeal) d.primeIdeal] at hunit'
  exact hunit' (two_mem_of_liesOver d.primeIdeal
    d.primeIdeal_liesOverTwo)

omit [Finite G] in
theorem card_zpowers_eq_two_of_isInvolution
    (s : G) (hs : IsInvolution s) :
    Nat.card (Subgroup.zpowers s) = 2 :=
  (Nat.card_zpowers s).trans (orderOf_eq_prime hs.2 hs.1)

private theorem localizedGroupAlgebraToComplex_injective
    (d : PrincipalCongruenceBlockData G) :
    Function.Injective (localizedGroupAlgebraToComplex d) := by
  intro x y hxy
  ext g
  apply localizationToComplex_injective d
  have hg := congrArg (fun z : MonoidAlgebra ℂ G => z g) hxy
  simpa [localizedGroupAlgebraToComplex,
    MonoidAlgebra.mapRingHom_apply] using hg

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
    ∑ g : G, principalBlockElement d g = 1 := by
  let rho0 : Representation ℂ G (Fin 1 → ℂ) :=
    Representation.trivial ℂ G (Fin 1 → ℂ)
  have hchar : d.chi d.principal = rho0.characterClassFunction := by
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
      (rho0.asAlgebraHom a (fun _ => 1)) 0 = ∑ g : G, a g := by
    induction a using MonoidAlgebra.induction_linear with
    | zero =>
        change 0 = ∑ _g : G, (0 : ℂ)
        simp
    | add a b ha hb =>
        simp only [map_add, LinearMap.add_apply, Pi.add_apply, ha, hb]
        change (∑ g : G, a g) + (∑ g : G, b g) =
          ∑ g : G, (a g + b g)
        rw [Finset.sum_add_distrib]
    | single g r => simp
  rw [hactionSum] at hone
  exact hone

theorem principalBlockElement_coeff_eq_localized
    (d : PrincipalCongruenceBlockData G) (g : G) :
    (principalBlockElement d).coeff g =
      localizationToComplex d.primeIdeal
        ((localizedPrincipalBlockElement d).coeff g) := by
  change (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
      (localizedPrincipalBlockElement d)) g =
    localizationToComplex d.primeIdeal
      ((localizedPrincipalBlockElement d) g)
  exact MonoidAlgebra.mapRingHom_apply _ _ _

/-- The integral-localized principal-block selector also has augmentation
one.  This is detected after embedding the localization into `ℂ`. -/
theorem localizedPrincipalBlockElement_sum_coeff_eq_one
    (d : PrincipalCongruenceBlockData G) :
    ∑ g : G, localizedPrincipalBlockElement d g = 1 := by
  apply localizationToComplex_injective d
  rw [map_one, map_sum]
  calc
    ∑ g : G, localizationToComplex d.primeIdeal
        (localizedPrincipalBlockElement d g) =
        ∑ g : G, principalBlockElement d g := by
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
    inv_eq_self_of_sq_eq_one (by simpa [pow_two] using hs.2)
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
  let S : Subgroup G := Subgroup.zpowers s
  letI : CommGroup S :=
    @IsCyclic.commGroup S inferInstance (inferInstance : IsCyclic S)
  let c : S := ⟨s, Subgroup.mem_zpowers s⟩
  have hc : c ≠ 1 := by
    intro h
    apply hs.1
    exact congrArg Subtype.val h
  have hsq : s * s = 1 := by
    simpa [pow_two] using hs.2
  have hphi : S.subtype c = s := rfl
  letI : IsLocalRing
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) S) :=
    CentralIdempotentSupport.isLocalRing_monoidAlgebra_of_card_two
      (two_not_isUnit_cyclotomicOrderAtPrime d)
      (by simpa [S] using card_zpowers_eq_two_of_isInvolution s hs)
  letI : Module.Projective
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) S)
      (CentralIdempotentSupport.restrictedRightIdealRepresentation
        (cyclotomicOrderAtPrime d.primeIdeal)
        (localizedPrincipalBlockElement d) S.subtype).asModule :=
    CentralIdempotentSupport.projective_restrictedRightIdeal_asModule
      (localizedPrincipalBlockElement d)
      (localizedPrincipalBlockElement_isIdempotent d) S
  letI : Module.Finite
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) S)
      (CentralIdempotentSupport.restrictedRightIdealRepresentation
        (cyclotomicOrderAtPrime d.primeIdeal)
        (localizedPrincipalBlockElement d) S.subtype).asModule :=
    CentralIdempotentSupport.finite_restrictedRightIdeal_asModule
      (localizedPrincipalBlockElement d)
      (localizedPrincipalBlockElement_isIdempotent d) S
  have hzero :=
    CentralIdempotentSupport.coeff_involution_eq_zero_of_projective_restriction_of_local
      (R := cyclotomicOrderAtPrime d.primeIdeal) (C := S) (G := G)
      S.subtype c hc s hphi hsq (localizedPrincipalBlockElement d)
      (localizedPrincipalBlockElement_isIdempotent d)
      (localizedPrincipalBlockElement_mem_center d)
  change localizedPrincipalBlockElement d s = 0
  exact hzero

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

end BlockIndicator

end BlockOrthogonality

end Submission.ZStar
