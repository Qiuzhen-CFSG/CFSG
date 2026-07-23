module

public import FeitThompson.PFsection1.PFsection1_1
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import FeitThompson.Representation.Unbundled
/-!
# Peterfalvi, Section 1, Proposition (1.3)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_3.tex`.

Current scope discipline:

* No Lean files outside `PFtest` are imported or read.
* The book-facing conjunction has been split into public main declarations;
  theorem-local core lemmas remain private.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section1
universe u
universe v

/-! ## Basic notation for Proposition (1.3) -/

@[expose]
public def scalarProduct (G : Type*) [Finite G] (phi psi : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, phi g * star (psi g)

public def supportedOn {G : Type*} (phi : ClassFunction G) (A : Set G) : Prop :=
  ∀ g, g ∉ A → phi g = 0

public theorem supportedOn_iff
    {G : Type*} {phi : ClassFunction G} {A : Set G} :
    supportedOn phi A ↔ ∀ g, g ∉ A → phi g = 0 :=
  Iff.rfl

public def classFunctionsOn (G : Type*) (A : Set G) : Submodule ℂ (ClassFunction G) where
  carrier := {phi | supportedOn phi A}
  zero_mem' _ _ := by simp
  add_mem' hphi hpsi g hg := by simp [hphi g hg, hpsi g hg]
  smul_mem' z phi hphi g hg := by simp [hphi g hg]

public theorem mem_classFunctionsOn
    {G : Type*} {A : Set G} {phi : ClassFunction G} :
    phi ∈ classFunctionsOn G A ↔ supportedOn phi A :=
  Iff.rfl

public def IsUnionOfConjugacyClasses {G : Type*} [Group G] (A : Set G) : Prop :=
  ∀ x g : G, g ∈ A → x * g * x⁻¹ ∈ A

public def classFunctionsOnClass (G : Type*) [Group G] (A : Set G) :
    Submodule ℂ (ClassFunction G) where
  carrier := {phi | IsClassFunction phi ∧ supportedOn phi A}
  zero_mem' := by
    constructor
    · unfold IsClassFunction
      intro x g
      simp
    · intro g hg
      simp
  add_mem' := by
    intro phi psi hphi hpsi
    constructor
    · have hphi_class : ∀ x g : G, phi (x * g * x⁻¹) = phi g := by
        simpa [IsClassFunction] using hphi.1
      have hpsi_class : ∀ x g : G, psi (x * g * x⁻¹) = psi g := by
        simpa [IsClassFunction] using hpsi.1
      change ∀ x g : G, (phi + psi) (x * g * x⁻¹) = (phi + psi) g
      intro x g
      simp [hphi_class x g, hpsi_class x g]
    · intro g hg
      simp [hphi.2 g hg, hpsi.2 g hg]
  smul_mem' := by
    intro z phi hphi
    constructor
    · have hphi_class : ∀ x g : G, phi (x * g * x⁻¹) = phi g := by
        simpa [IsClassFunction] using hphi.1
      change ∀ x g : G, (z • phi) (x * g * x⁻¹) = (z • phi) g
      intro x g
      simp [hphi_class x g]
    · intro g hg
      simp [hphi.2 g hg]

public theorem mem_classFunctionsOnClass
    {G : Type*} [Group G] {A : Set G} {phi : ClassFunction G} :
    phi ∈ classFunctionsOnClass G A ↔ IsClassFunction phi ∧ supportedOn phi A :=
  Iff.rfl

public def eqOnSet {G : Type*} (A : Set G) (phi psi : ClassFunction G) : Prop :=
  ∀ g ∈ A, phi g = psi g

public def restrictClassFunction {G : Type*} [Group G] (H : Subgroup G) :
    ClassFunction G →ₗ[ℂ] ClassFunction H where
  toFun mu := fun h => mu h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public def deltaFunction {H : Type*} [DecidableEq H] (a : H) : ClassFunction H :=
  fun x => if x = a then 1 else 0

@[expose] public noncomputable def conjugacyClassProjection
    {H : Type*} [Group H] (a : H) : ClassFunction H := by
  classical
  exact fun x =>
    if ConjClasses.mk x = ConjClasses.mk a then
      (Nat.card H : ℂ) / (Nat.card (ConjClasses.mk a).carrier : ℂ)
    else 0

/-! ## Small linear-algebra nodes for Proposition (1.3) -/

lemma isClassFunction_restrictClassFunction
    {G : Type*} [Group G] (H : Subgroup G) {mu : ClassFunction G}
    (hmu : IsClassFunction mu) :
    IsClassFunction (restrictClassFunction H mu) := by
  unfold IsClassFunction at hmu ⊢
  intro x g
  simp [restrictClassFunction]
  simpa using hmu (x : G) (g : G)

lemma isClassFunction_sum_smul
    {H I : Type*} [Group H] [Fintype I]
    (chi : I → ClassFunction H) (d : I → ℂ)
    (hchi : ∀ i, IsClassFunction (chi i)) :
    IsClassFunction (∑ i, d i • chi i) := by
  unfold IsClassFunction
  intro x g
  have hterm : ∀ i, d i * chi i (x * (g * x⁻¹)) = d i * chi i g := by
    intro i
    rw [show x * (g * x⁻¹) = x * g * x⁻¹ by group, hchi i x g]
  simpa [Finset.mul_sum, mul_assoc] using
    (Finset.sum_congr rfl (fun i _ => hterm i))

lemma isClassFunction_sub
    {H : Type*} [Group H] {phi psi : ClassFunction H}
    (hphi : IsClassFunction phi) (hpsi : IsClassFunction psi) :
    IsClassFunction (phi - psi) := by
  unfold IsClassFunction at hphi hpsi ⊢
  intro x g
  simp [hphi x g, hpsi x g]

lemma conjugacyClassProjection_isClassFunction
    {H : Type*} [Group H] (a : H) :
    IsClassFunction (conjugacyClassProjection a) := by
  classical
  unfold IsClassFunction
  intro x g
  have hmk : ConjClasses.mk (x * g * x⁻¹) = ConjClasses.mk g := by
    apply ConjClasses.mk_eq_mk_iff_isConj.2
    rw [isConj_iff]
    refine ⟨x⁻¹, ?_⟩
    simp [mul_assoc]
  simp [conjugacyClassProjection, hmk]

lemma conjugacyClassProjection_supportedOn
    {H : Type*} [Group H]
    {A : Set H} (hA : IsUnionOfConjugacyClasses A) {a : H} (ha : a ∈ A) :
    supportedOn (conjugacyClassProjection a) A := by
  classical
  intro g hg
  by_cases hmk : ConjClasses.mk g = ConjClasses.mk a
  · have hconj : IsConj a g := ConjClasses.mk_eq_mk_iff_isConj.mp hmk.symm
    rcases isConj_iff.mp hconj with ⟨u, hu⟩
    have huga : u * a * u⁻¹ = g := hu
    have hgA : g ∈ A := by
      simpa [huga] using hA u a ha
    exact (hg hgA).elim
  · simp [conjugacyClassProjection, hmk]

lemma scalarProduct_conjugacyClassProjection_left
    {H : Type*} [Group H] [Finite H]
    (a : H) (phi : ClassFunction H) (hphi : IsClassFunction phi) :
    scalarProduct H (conjugacyClassProjection a) phi = star (phi a) := by
  classical
  have hphi_eq : ∀ x : H, ConjClasses.mk x = ConjClasses.mk a → phi x = phi a := by
    intro x hx
    have hconj : IsConj x a := ConjClasses.mk_eq_mk_iff_isConj.mp hx
    rcases isConj_iff.mp hconj with ⟨u, hu⟩
    have huxa : u * x * u⁻¹ = a := hu
    have hphi' : ∀ x g : H, phi (x * g * x⁻¹) = phi g := by
      simpa [IsClassFunction] using hphi
    calc
      phi x = phi (u * x * u⁻¹) := by simpa using (hphi' u x).symm
      _ = phi a := by rw [huxa]
  simp only [scalarProduct, conjugacyClassProjection]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hcard :
      (Finset.univ.filter (fun g : H => ConjClasses.mk g = ConjClasses.mk a)).card =
        Nat.card (ConjClasses.mk a).carrier := by
    rw [← Fintype.card_subtype]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun g : H =>
      (ConjClasses.mem_carrier_iff_mk_eq
        (a := g) (b := ConjClasses.mk a)).symm))
  trans (Nat.card H : ℂ)⁻¹ *
      ((Finset.univ.filter (fun g : H => ConjClasses.mk g = ConjClasses.mk a)).card •
        ((Nat.card H : ℂ) / (Nat.card (ConjClasses.mk a).carrier : ℂ) *
          star (phi a)))
  · congr 1
    calc
      ∑ x ∈ Finset.univ with ConjClasses.mk x = ConjClasses.mk a,
          (Nat.card H : ℂ) / (Nat.card (ConjClasses.mk a).carrier : ℂ) *
            star (phi x)
        = ∑ x ∈ Finset.univ with ConjClasses.mk x = ConjClasses.mk a,
            (Nat.card H : ℂ) / (Nat.card (ConjClasses.mk a).carrier : ℂ) *
              star (phi a) := by
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            rw [hphi_eq g hg]
      _ = (Finset.univ.filter (fun g : H => ConjClasses.mk g = ConjClasses.mk a)).card •
          ((Nat.card H : ℂ) / (Nat.card (ConjClasses.mk a).carrier : ℂ) *
            star (phi a)) := by
            rw [Finset.sum_const]
  · rw [hcard]
    have hH : (Nat.card H : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := H)).ne'
    have hclass_nonempty : Nonempty (ConjClasses.mk a).carrier :=
      ⟨⟨a, ConjClasses.mem_carrier_mk⟩⟩
    have hclass : (Nat.card (ConjClasses.mk a).carrier : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk a).carrier)).ne'
    rw [nsmul_eq_mul]
    field_simp [hH, hclass]

lemma eqOnSet_iff_sub_supportedOn_compl
    {H : Type*} [Finite H]
    (A : Set H) (phi psi : ClassFunction H) :
    eqOnSet A phi psi ↔ supportedOn (phi - psi) Aᶜ := by
  constructor
  · intro h g hg
    have hgA : g ∈ A := by simpa using hg
    simpa [Pi.sub_apply, sub_eq_zero] using h g hgA
  · intro h g hg
    have hgc : g ∉ Aᶜ := by simpa using hg
    simpa [Pi.sub_apply, sub_eq_zero] using h g hgc

lemma scalarProduct_zero_left
    {H : Type*} [Finite H] (phi : ClassFunction H) :
    scalarProduct H 0 phi = 0 := by
  simp [scalarProduct]

lemma scalarProduct_zero_right
    {H : Type*} [Finite H] (phi : ClassFunction H) :
    scalarProduct H phi 0 = 0 := by
  simp [scalarProduct]

lemma scalarProduct_add_left
    {H : Type*} [Finite H] (phi1 phi2 psi : ClassFunction H) :
    scalarProduct H (phi1 + phi2) psi =
      scalarProduct H phi1 psi + scalarProduct H phi2 psi := by
  simp [scalarProduct, mul_add, Finset.sum_add_distrib, right_distrib]

lemma scalarProduct_smul_left
    {H : Type*} [Finite H] (z : ℂ) (phi psi : ClassFunction H) :
    scalarProduct H (z • phi) psi = z * scalarProduct H phi psi := by
  calc
    scalarProduct H (z • phi) psi
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, z * (phi g * star (psi g)) := by
            simp [scalarProduct, mul_assoc]
    _ = (Nat.card H : ℂ)⁻¹ * (z * ∑ g : H, phi g * star (psi g)) := by
          rw [← Finset.mul_sum]
    _ = z * scalarProduct H phi psi := by
          simp [scalarProduct, mul_left_comm]

lemma scalarProduct_add_right
    {H : Type*} [Finite H] (phi psi1 psi2 : ClassFunction H) :
    scalarProduct H phi (psi1 + psi2) =
      scalarProduct H phi psi1 + scalarProduct H phi psi2 := by
  simp [scalarProduct, mul_add, Finset.sum_add_distrib]

lemma scalarProduct_smul_right
    {H : Type*} [Finite H] (z : ℂ) (phi psi : ClassFunction H) :
    scalarProduct H phi (z • psi) = scalarProduct H phi psi * star z := by
  calc
    scalarProduct H phi (z • psi)
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, (phi g * star (psi g)) * star z := by
            unfold scalarProduct
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp [mul_left_comm, mul_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((∑ g : H, phi g * star (psi g)) * star z) := by
          rw [Finset.sum_mul]
    _ = scalarProduct H phi psi * star z := by
          simp [scalarProduct, mul_left_comm, mul_comm]

lemma scalarProduct_sub_right
    {H : Type*} [Finite H] (phi psi1 psi2 : ClassFunction H) :
    scalarProduct H phi (psi1 - psi2) =
      scalarProduct H phi psi1 - scalarProduct H phi psi2 := by
  calc
    scalarProduct H phi (psi1 - psi2)
        = scalarProduct H phi (psi1 + (-1 : ℂ) • psi2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = scalarProduct H phi psi1 + scalarProduct H phi ((-1 : ℂ) • psi2) := by
          rw [scalarProduct_add_right]
    _ = scalarProduct H phi psi1 - scalarProduct H phi psi2 := by
          rw [scalarProduct_smul_right]
          simp [sub_eq_add_neg]

lemma scalarProduct_sum_left
    {H I : Type*} [Finite H] [Fintype I]
    (psi : ClassFunction H) (d : I → ℂ) (phi : I → ClassFunction H) :
    scalarProduct H (∑ i, d i • phi i) psi =
      ∑ i, d i * scalarProduct H (phi i) psi := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp [scalarProduct_zero_left]
  | @insert i s hi hs =>
      simp [hi, scalarProduct_add_left, scalarProduct_smul_left, hs]

lemma scalarProduct_sum_right
    {H I : Type*} [Finite H] [Fintype I]
    (phi : ClassFunction H) (d : I → ℂ) (psi : I → ClassFunction H) :
    scalarProduct H phi (∑ i, d i • psi i) =
      ∑ i, scalarProduct H phi (psi i) * star (d i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp [scalarProduct_zero_right]
  | @insert i s hi hs =>
      simp [hi, scalarProduct_add_right, scalarProduct_smul_right, hs]

lemma supportedOn_basis
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (classFunctionsOn H A)) (j : J) :
    supportedOn (basis j : ClassFunction H) A :=
  (basis j).property

lemma classFunctionsOnClass_isClassFunction_basis
    {H J : Type*} [Group H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (classFunctionsOnClass H A)) (j : J) :
    IsClassFunction (basis j : ClassFunction H) :=
  (basis j).property.1

lemma classFunctionsOnClass_supportedOn_basis
    {H J : Type*} [Group H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (classFunctionsOnClass H A)) (j : J) :
    supportedOn (basis j : ClassFunction H) A :=
  (basis j).property.2

lemma scalarProduct_eq_zero_of_support_disjoint
    {H : Type*} [Finite H]
    {A : Set H} {phi psi : ClassFunction H}
    (hphi : supportedOn phi A)
    (hpsi : supportedOn psi Aᶜ) :
    scalarProduct H phi psi = 0 := by
  have hsum : ∑ g : H, phi g * star (psi g) = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro g hg
    by_cases hgA : g ∈ A
    · have hgAc : g ∉ Aᶜ := by simpa using hgA
      have hzero : psi g = 0 := hpsi g hgAc
      simp [hzero]
    · have hzero : phi g = 0 := hphi g hgA
      simp [hzero]
  rw [scalarProduct, hsum]
  simp

lemma basis_test_iff_orthogonalTo_subspace
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (classFunctionsOn H A))
    (eta : ClassFunction H) :
    (∀ j, scalarProduct H (basis j : ClassFunction H) eta = 0) ↔
      ∀ phi ∈ classFunctionsOn H A, scalarProduct H phi eta = 0 := by
  constructor
  · intro h phi hphi
    let x : classFunctionsOn H A := ⟨phi, hphi⟩
    let L : classFunctionsOn H A →ₗ[ℂ] ℂ :=
      { toFun := fun psi => scalarProduct H (psi : ClassFunction H) eta
        map_add' := by
          intro psi1 psi2
          exact scalarProduct_add_left (psi1 : ClassFunction H) (psi2 : ClassFunction H) eta
        map_smul' := by
          intro z psi
          exact scalarProduct_smul_left z (psi : ClassFunction H) eta }
    have hLbasis : ∀ j, L (basis j) = 0 := by
      intro j
      simpa [L] using h j
    change L x = 0
    calc
      L x = L (∑ j, basis.repr x j • basis j) := by rw [basis.sum_repr x]
      _ = ∑ j, L (basis.repr x j • basis j) := by rw [map_sum]
      _ = ∑ j, basis.repr x j • L (basis j) := by simp
      _ = 0 := by simp [hLbasis]
  · intro h j
    exact h (basis j) (by simp)

lemma basis_test_iff_orthogonalTo_classSubspace
    {H J : Type*} [Group H] [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (classFunctionsOnClass H A))
    (eta : ClassFunction H) :
    (∀ j, scalarProduct H (basis j : ClassFunction H) eta = 0) ↔
      ∀ phi ∈ classFunctionsOnClass H A, scalarProduct H phi eta = 0 := by
  constructor
  · intro h phi hphi
    let x : classFunctionsOnClass H A := ⟨phi, hphi⟩
    let L : classFunctionsOnClass H A →ₗ[ℂ] ℂ :=
      { toFun := fun psi => scalarProduct H (psi : ClassFunction H) eta
        map_add' := by
          intro psi1 psi2
          exact scalarProduct_add_left (psi1 : ClassFunction H) (psi2 : ClassFunction H) eta
        map_smul' := by
          intro z psi
          exact scalarProduct_smul_left z (psi : ClassFunction H) eta }
    have hLbasis : ∀ j, L (basis j) = 0 := by
      intro j
      simpa [L] using h j
    change L x = 0
    calc
      L x = L (∑ j, basis.repr x j • basis j) := by rw [basis.sum_repr x]
      _ = ∑ j, L (basis.repr x j • basis j) := by rw [map_sum]
      _ = ∑ j, basis.repr x j • L (basis j) := by simp
      _ = 0 := by simp [hLbasis]
  · intro h j
    exact h (basis j) (by simp)

lemma deltaFunction_supportedOn
    {H : Type*} [Finite H] [DecidableEq H]
    {A : Set H} {a : H} (ha : a ∈ A) :
    supportedOn (deltaFunction a) A := by
  intro g hg
  by_cases hga : g = a
  · exfalso
    apply hg
    simpa [hga] using ha
  · simp [deltaFunction, hga]

lemma scalarProduct_delta_left
    {H : Type*} [Finite H] [DecidableEq H]
    (a : H) (phi : ClassFunction H) :
    scalarProduct H (deltaFunction a) phi =
      (Nat.card H : ℂ)⁻¹ * star (phi a) := by
  simp [scalarProduct, deltaFunction]

/-! ## Proposition (1.3) -/

lemma proposition_1_3_a_core
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [Finite H]
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J]
    (basis : Module.Basis J ℂ (classFunctionsOn H A))
    (chi : I → ClassFunction H)
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (mu : ClassFunction G) (d : I → ℂ) :
    eqOnSet A (restrictClassFunction H mu) (∑ i, d i • chi i) ↔
      ∀ j,
        ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) =
          scalarProduct G (ind (basis j : ClassFunction H)) mu := by
  let rhs : ClassFunction H := ∑ i, d i • chi i
  let diff : ClassFunction H := restrictClassFunction H mu - rhs
  have hsupport :
      eqOnSet A (restrictClassFunction H mu) rhs ↔ supportedOn diff Aᶜ := by
    simpa [diff, rhs] using
      eqOnSet_iff_sub_supportedOn_compl A (restrictClassFunction H mu) rhs
  constructor
  · intro hEq j
    have hzero :
        scalarProduct H (basis j : ClassFunction H) diff = 0 := by
      exact scalarProduct_eq_zero_of_support_disjoint
        (supportedOn_basis basis j) ((hsupport.mp hEq))
    have hexpand :
        scalarProduct H (basis j : ClassFunction H) diff =
          scalarProduct G (ind (basis j : ClassFunction H)) mu -
            ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) := by
      simp [diff, rhs, hfrob, scalarProduct_sub_right, scalarProduct_sum_right]
    have hmain :
        scalarProduct G (ind (basis j : ClassFunction H)) mu -
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) = 0 := by
      simpa [hexpand] using hzero
    exact (sub_eq_zero.mp hmain).symm
  · intro hCoeff
    have hBasisZero :
        ∀ j, scalarProduct H (basis j : ClassFunction H) diff = 0 := by
      intro j
      have hj := hCoeff j
      have hmain :
          scalarProduct G (ind (basis j : ClassFunction H)) mu -
            ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) = 0 := by
        exact sub_eq_zero.mpr hj.symm
      simpa [diff, rhs, hfrob, scalarProduct_sub_right, scalarProduct_sum_right] using hmain
    have hAllZero :
        ∀ phi ∈ classFunctionsOn H A, scalarProduct H phi diff = 0 :=
      (basis_test_iff_orthogonalTo_subspace basis diff).mp hBasisZero
    have hcard : (Nat.card H : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card H ≠ 0)
    rw [hsupport]
    intro a ha
    classical
    have haA : a ∈ A := by
      simpa using ha
    have hdelta :
        scalarProduct H (deltaFunction a) diff = 0 := by
      exact hAllZero (deltaFunction a) (deltaFunction_supportedOn haA)
    have hpoint :
        diff a = 0 := by
      rw [scalarProduct_delta_left] at hdelta
      rcases mul_eq_zero.mp hdelta with hbad | hstar
      · exact (inv_ne_zero hcard hbad).elim
      · exact star_eq_zero.mp hstar
    simpa [diff, rhs, sub_eq_zero] using hpoint

lemma proposition_1_3_b_core
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [Finite H]
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (basis : Module.Basis J ℂ (classFunctionsOn H A))
    (chi : I → ClassFunction H)
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    (∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i)) ∧
      ∀ mu, (∀ i, scalarProduct G (muFam i) mu = 0) →
        eqOnSet A (restrictClassFunction H mu) 0 := by
  have h_first :
      ∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i) := by
    intro i
    have hs :
        (∑ k, (if k = i then (1 : ℂ) else 0) • chi k) = chi i := by
      classical
      simp
    have hi :
        eqOnSet A (restrictClassFunction H (muFam i))
          (∑ k, (if k = i then (1 : ℂ) else 0) • chi k) := by
      refine (proposition_1_3_a_core basis chi ind hfrob (muFam i)
        (fun k => if k = i then (1 : ℂ) else 0)).mpr ?_
      intro j
      calc
        ∑ k, scalarProduct H (basis j : ClassFunction H) (chi k) *
            star (if k = i then 1 else 0)
            = scalarProduct G (∑ k,
                scalarProduct H (basis j : ClassFunction H) (chi k) • muFam k) (muFam i) := by
                rw [scalarProduct_sum_left]
                simp [h_orthonormal]
        _ = scalarProduct G (ind (basis j : ClassFunction H)) (muFam i) := by
            rw [← h_expand j]
    simpa [hs] using hi
  have h_second :
      ∀ mu, (∀ i, scalarProduct G (muFam i) mu = 0) →
        eqOnSet A (restrictClassFunction H mu) 0 := by
    intro mu hmu
    have hs :
        (∑ i, (0 : ℂ) • chi i) = 0 := by
      simp
    have hzero :
        eqOnSet A (restrictClassFunction H mu) (∑ i, (0 : ℂ) • chi i) := by
      refine (proposition_1_3_a_core basis chi ind hfrob mu (fun _ => 0)).mpr ?_
      intro j
      calc
        ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (0 : ℂ) = 0 := by
          simp
        _ = scalarProduct G (∑ i,
              scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i) mu := by
            rw [scalarProduct_sum_left]
            simp [hmu]
        _ = scalarProduct G (ind (basis j : ClassFunction H)) mu := by
            rw [← h_expand j]
    simpa [hs] using hzero
  exact ⟨h_first, h_second⟩

lemma proposition_1_3_a_class_core
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [Finite H]
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J]
    (hA : IsUnionOfConjugacyClasses A)
    (basis : Module.Basis J ℂ (classFunctionsOnClass H A))
    (chi : I → ClassFunction H)
    (hchiClass : ∀ i, IsClassFunction (chi i))
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (mu : ClassFunction G) (hmuClass : IsClassFunction mu) (d : I → ℂ) :
    eqOnSet A (restrictClassFunction H mu) (∑ i, d i • chi i) ↔
      ∀ j,
        ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) =
          scalarProduct G (ind (basis j : ClassFunction H)) mu := by
  let rhs : ClassFunction H := ∑ i, d i • chi i
  let diff : ClassFunction H := restrictClassFunction H mu - rhs
  have hsupport :
      eqOnSet A (restrictClassFunction H mu) rhs ↔ supportedOn diff Aᶜ := by
    simpa [diff, rhs] using
      eqOnSet_iff_sub_supportedOn_compl A (restrictClassFunction H mu) rhs
  have hdiffClass : IsClassFunction diff := by
    exact isClassFunction_sub
      (isClassFunction_restrictClassFunction H hmuClass)
      (isClassFunction_sum_smul chi d hchiClass)
  constructor
  · intro hEq j
    have hzero :
        scalarProduct H (basis j : ClassFunction H) diff = 0 := by
      exact scalarProduct_eq_zero_of_support_disjoint
        (classFunctionsOnClass_supportedOn_basis basis j) ((hsupport.mp hEq))
    have hexpand :
        scalarProduct H (basis j : ClassFunction H) diff =
          scalarProduct G (ind (basis j : ClassFunction H)) mu -
            ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) := by
      simp [diff, rhs, hfrob, scalarProduct_sub_right, scalarProduct_sum_right]
    have hmain :
        scalarProduct G (ind (basis j : ClassFunction H)) mu -
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) = 0 := by
      simpa [hexpand] using hzero
    exact (sub_eq_zero.mp hmain).symm
  · intro hCoeff
    have hBasisZero :
        ∀ j, scalarProduct H (basis j : ClassFunction H) diff = 0 := by
      intro j
      have hj := hCoeff j
      have hmain :
          scalarProduct G (ind (basis j : ClassFunction H)) mu -
            ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) = 0 := by
        exact sub_eq_zero.mpr hj.symm
      simpa [diff, rhs, hfrob, scalarProduct_sub_right, scalarProduct_sum_right] using hmain
    have hAllZero :
        ∀ phi ∈ classFunctionsOnClass H A, scalarProduct H phi diff = 0 :=
      (basis_test_iff_orthogonalTo_classSubspace basis diff).mp hBasisZero
    rw [hsupport]
    intro a ha
    classical
    have haA : a ∈ A := by
      simpa using ha
    have hproj_mem : conjugacyClassProjection a ∈ classFunctionsOnClass H A := by
      exact (mem_classFunctionsOnClass).2
        ⟨conjugacyClassProjection_isClassFunction a,
          conjugacyClassProjection_supportedOn hA haA⟩
    have hproj :
        scalarProduct H (conjugacyClassProjection a) diff = 0 :=
      hAllZero (conjugacyClassProjection a) hproj_mem
    have hpoint : diff a = 0 := by
      rw [scalarProduct_conjugacyClassProjection_left a diff hdiffClass] at hproj
      exact star_eq_zero.mp hproj
    simpa [diff, rhs, sub_eq_zero] using hpoint

lemma proposition_1_3_b_class_core
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [Finite H]
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (hA : IsUnionOfConjugacyClasses A)
    (basis : Module.Basis J ℂ (classFunctionsOnClass H A))
    (chi : I → ClassFunction H)
    (hchiClass : ∀ i, IsClassFunction (chi i))
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (hmuFamClass : ∀ i, IsClassFunction (muFam i))
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    (∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i)) ∧
      ∀ mu, IsClassFunction mu → (∀ i, scalarProduct G (muFam i) mu = 0) →
        eqOnSet A (restrictClassFunction H mu) 0 := by
  have h_first :
      ∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i) := by
    intro i
    have hs :
        (∑ k, (if k = i then (1 : ℂ) else 0) • chi k) = chi i := by
      classical
      simp
    have hi :
        eqOnSet A (restrictClassFunction H (muFam i))
          (∑ k, (if k = i then (1 : ℂ) else 0) • chi k) := by
      refine (proposition_1_3_a_class_core hA basis chi hchiClass ind hfrob
        (muFam i) (hmuFamClass i)
        (fun k => if k = i then (1 : ℂ) else 0)).mpr ?_
      intro j
      calc
        ∑ k, scalarProduct H (basis j : ClassFunction H) (chi k) *
            star (if k = i then 1 else 0)
            = scalarProduct G (∑ k,
                scalarProduct H (basis j : ClassFunction H) (chi k) • muFam k) (muFam i) := by
                rw [scalarProduct_sum_left]
                simp [h_orthonormal]
        _ = scalarProduct G (ind (basis j : ClassFunction H)) (muFam i) := by
            rw [← h_expand j]
    simpa [hs] using hi
  have h_second :
      ∀ mu, IsClassFunction mu → (∀ i, scalarProduct G (muFam i) mu = 0) →
        eqOnSet A (restrictClassFunction H mu) 0 := by
    intro mu hmuClass hmu
    have hs :
        (∑ i, (0 : ℂ) • chi i) = 0 := by
      simp
    have hzero :
        eqOnSet A (restrictClassFunction H mu) (∑ i, (0 : ℂ) • chi i) := by
      refine (proposition_1_3_a_class_core hA basis chi hchiClass ind hfrob
        mu hmuClass (fun _ => 0)).mpr ?_
      intro j
      calc
        ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (0 : ℂ) = 0 := by
          simp
        _ = scalarProduct G (∑ i,
              scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i) mu := by
            rw [scalarProduct_sum_left]
            simp [hmu]
        _ = scalarProduct G (ind (basis j : ClassFunction H)) mu := by
            rw [← h_expand j]
    simpa [hs] using hzero
  exact ⟨h_first, h_second⟩

public theorem proposition_1_3_a_support
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J]
    (basis : Module.Basis J ℂ (classFunctionsOn H A))
    (chi : I → ClassFunction H)
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (mu : ClassFunction G) (d : I → ℂ) :
    eqOnSet A (restrictClassFunction H mu) (∑ i, d i • chi i) ↔
      ∀ j,
        ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) =
          scalarProduct G (ind (basis j : ClassFunction H)) mu :=
  proposition_1_3_a_core basis chi ind hfrob mu d

public theorem proposition_1_3_b_support
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (basis : Module.Basis J ℂ (classFunctionsOn H A))
    (chi : I → ClassFunction H)
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    (∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i)) ∧
      ∀ mu, (∀ i, scalarProduct G (muFam i) mu = 0) →
        eqOnSet A (restrictClassFunction H mu) 0 :=
  proposition_1_3_b_core basis chi ind hfrob muFam h_expand h_orthonormal

public theorem proposition_1_3_b_restriction_support
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (basis : Module.Basis J ℂ (classFunctionsOn H A))
    (chi : I → ClassFunction H)
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    ∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i) :=
  (proposition_1_3_b_support basis chi ind hfrob muFam h_expand h_orthonormal).1

public theorem proposition_1_3_c_support
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (basis : Module.Basis J ℂ (classFunctionsOn H A))
    (chi : I → ClassFunction H)
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    ∀ mu, (∀ i, scalarProduct G (muFam i) mu = 0) →
      eqOnSet A (restrictClassFunction H mu) 0 :=
  (proposition_1_3_b_support basis chi ind hfrob muFam h_expand h_orthonormal).2

public theorem proposition_1_3_a
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J]
    (hA : IsUnionOfConjugacyClasses A)
    (basis : Module.Basis J ℂ (classFunctionsOnClass H A))
    (chi : I → ClassFunction H)
    (hchiClass : ∀ i, IsClassFunction (chi i))
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (mu : ClassFunction G) (hmuClass : IsClassFunction mu) (d : I → ℂ) :
    eqOnSet A (restrictClassFunction H mu) (∑ i, d i • chi i) ↔
      ∀ j,
        ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) * star (d i) =
          scalarProduct G (ind (basis j : ClassFunction H)) mu :=
  proposition_1_3_a_class_core hA basis chi hchiClass ind hfrob mu hmuClass d

public theorem proposition_1_3_b
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (hA : IsUnionOfConjugacyClasses A)
    (basis : Module.Basis J ℂ (classFunctionsOnClass H A))
    (chi : I → ClassFunction H)
    (hchiClass : ∀ i, IsClassFunction (chi i))
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (hmuFamClass : ∀ i, IsClassFunction (muFam i))
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    (∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i)) ∧
      ∀ mu, IsClassFunction mu → (∀ i, scalarProduct G (muFam i) mu = 0) →
        eqOnSet A (restrictClassFunction H mu) 0 :=
  proposition_1_3_b_class_core hA basis chi hchiClass ind hfrob muFam
    hmuFamClass h_expand h_orthonormal

public theorem proposition_1_3_b_restriction
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (hA : IsUnionOfConjugacyClasses A)
    (basis : Module.Basis J ℂ (classFunctionsOnClass H A))
    (chi : I → ClassFunction H)
    (hchiClass : ∀ i, IsClassFunction (chi i))
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (hmuFamClass : ∀ i, IsClassFunction (muFam i))
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    ∀ i, eqOnSet A (restrictClassFunction H (muFam i)) (chi i) :=
  (proposition_1_3_b hA basis chi hchiClass ind hfrob muFam hmuFamClass
    h_expand h_orthonormal).1

public theorem proposition_1_3_c
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G}
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (hA : IsUnionOfConjugacyClasses A)
    (basis : Module.Basis J ℂ (classFunctionsOnClass H A))
    (chi : I → ClassFunction H)
    (hchiClass : ∀ i, IsClassFunction (chi i))
    (ind : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hfrob : ∀ alpha mu,
      scalarProduct G (ind alpha) mu =
        scalarProduct H alpha (restrictClassFunction H mu))
    (muFam : I → ClassFunction G)
    (hmuFamClass : ∀ i, IsClassFunction (muFam i))
    (h_expand :
      ∀ j,
        ind (basis j : ClassFunction H) =
          ∑ i, scalarProduct H (basis j : ClassFunction H) (chi i) • muFam i)
    (h_orthonormal :
      ∀ i k, scalarProduct G (muFam i) (muFam k) = if i = k then 1 else 0) :
    ∀ mu, IsClassFunction mu → (∀ i, scalarProduct G (muFam i) mu = 0) →
      eqOnSet A (restrictClassFunction H mu) 0 :=
  (proposition_1_3_b hA basis chi hchiClass ind hfrob muFam hmuFamClass
    h_expand h_orthonormal).2

end Section1
