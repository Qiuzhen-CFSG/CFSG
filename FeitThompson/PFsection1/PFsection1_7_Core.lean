module

public import FeitThompson.PFsection1.PFsection1_6
public import FeitThompson.Representation.Induction
public import FeitThompson.Representation.Orthogonality
public import FeitThompson.Representation.SimpleCriteria
public import FeitThompson.Representation.Divisibility
public import FeitThompson.Representation.CharacterValues
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.Index
/-!
# Peterfalvi, Section 1, Proposition (1.7)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_7.tex`.

Current scope discipline:

* Proposition (1.5) supplies the already formalized class-function induction
  infrastructure used here.
* No Lean files outside `PFtest` are imported or read.
* This file records honest finite-sum and multiplicity infrastructure for
  Proposition (1.7).
* The old top-level wrapper has been removed. The current public declarations
  are split nodes recording the interface-level consequences that remain
  blocked on the external Isaacs dependencies.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section1

universe u v

/-! ## Basic notation for Proposition (1.7) -/

@[expose] public def familySum {G ι : Type*} [Finite ι]
    (Phi : ι → ClassFunction G) : ClassFunction G :=
  fun g => ∑ i : ι, Phi i g

@[expose] public def weightedFamilySum {G ι : Type*} [Finite ι]
    (w : ι → ℂ) (Phi : ι → ClassFunction G) : ClassFunction G :=
  fun g => ∑ i : ι, w i * Phi i g

public theorem weightedFamilySum_congr
    {G ι : Type*} [Finite ι]
    (w : ι → ℂ) (Phi Psi : ι → ClassFunction G)
    (h : ∀ i : ι, Phi i = Psi i) :
    weightedFamilySum w Phi = weightedFamilySum w Psi := by
  ext g
  simp [weightedFamilySum, h]

@[expose] public def IsCharacter {G : Type u} [Group G] [Finite G]
    (chi : ClassFunction G) : Prop :=
  ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module ℂ V,
    ∃ _ : FiniteDimensional ℂ V, ∃ rho : Representation ℂ G V,
      chi = rho.character

@[expose] public def IsBookIrreducibleCharacter {G : Type u} [Group G] [Finite G]
    (chi : ClassFunction G) : Prop :=
  IsCharacter chi ∧ IsIrreducibleCharacter chi

public theorem isCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsCharacter chi) :
    IsClassFunction chi := by
  rcases hchi with ⟨V, _hadd, _hmod, _hfd, rho, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := rho) g x

public theorem isBookIrreducibleCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    IsClassFunction chi :=
  isCharacter_isClassFunction chi hchi.1

public theorem degree_representation_character
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    degree rho.character = (Module.finrank ℂ V : ℂ) := by
  simp [degree, Representation.character]

public theorem degree_ne_zero_of_isBookIrreducibleCharacter
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    degree chi ≠ 0 := by
  rcases hchi with ⟨hchar, hirr⟩
  rcases hchar with ⟨V, _hadd, _hmod, _hfd, rho, hχ⟩
  intro hdegree
  have hfinC : (Module.finrank ℂ V : ℂ) = 0 := by
    rw [hχ, degree_representation_character rho] at hdegree
    exact hdegree
  have hfin : Module.finrank ℂ V = 0 := by
    exact_mod_cast hfinC
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp hfin
  have hχzero : chi = 0 := by
    rw [hχ]
    funext g
    have hzero : (rho g : V →ₗ[ℂ] V) = 0 := by
      ext v
      exact hsub.elim _ _
    simp [Representation.character, hzero]
  rw [hχzero] at hirr
  change scalarProduct G (0 : ClassFunction G) 0 = 1 at hirr
  simp [scalarProduct] at hirr

public theorem isBookIrreducibleCharacter_representation_witness_irreducible
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module ℂ V,
      ∃ _ : FiniteDimensional ℂ V, ∃ rho : Representation ℂ G V,
        chi = rho.character ∧ Representation.IsIrreducible rho := by
  rcases hchi with ⟨hchar, hirr⟩
  rcases hchar with ⟨V, _hadd, _hmod, _hfd, rho, hχ⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, rho, hχ, ?_⟩
  classical
  apply (Representation.irreducible_iff_end_dimension_one (ρ := rho)).2
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  have hnorm :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          rho.character g * rho.character g⁻¹ = 1 := by
    calc
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          rho.character g * rho.character g⁻¹ =
          scalarProduct G rho.character rho.character := by
            unfold scalarProduct
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g _hg
            rw [representation_character_inv_eq_star_character rho g]
      _ = 1 := by
            simpa [hχ] using hirr
  have hfinC :
      (Module.finrank ℂ (Representation.IntertwiningMap rho rho) : ℂ) = 1 := by
    calc
      (Module.finrank ℂ (Representation.IntertwiningMap rho rho) : ℂ) =
          (Nat.card G : ℂ)⁻¹ * ∑ g : G,
            rho.character g * rho.character g⁻¹ := by
            simpa using
              (Representation.card_inv_mul_sum_char_mul_char_eq_finrank
                (ρ := rho) (σ := rho)).symm
      _ = 1 := hnorm
  exact_mod_cast hfinC

public theorem degree_nat_dvd_card_of_isBookIrreducibleCharacter
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    ∃ d : ℕ, degree chi = (d : ℂ) ∧ d ∣ Nat.card G := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible chi hchi with
    ⟨V, _hadd, _hmod, _hfd, rho, hχ, hirr⟩
  refine ⟨Module.finrank ℂ V, ?_, ?_⟩
  · rw [hχ, degree_representation_character rho]
  · letI : Representation.IsIrreducible rho := hirr
    exact Representation.irreducible_dimension_dvd_group_order rho

public theorem isCharacter_inducedCF_of_isCharacter
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S] (psi : ClassFunction S)
    (hpsi : IsCharacter psi) :
  IsCharacter (inducedCF S psi) := by
  rcases hpsi with ⟨V, _hadd, _hmod, _hfd, rho, hpsi⟩
  haveI : FiniteDimensional ℂ (Representation.IndV S.subtype rho) :=
    Representation.finiteDimensional_ind S rho
  refine ⟨Representation.IndV S.subtype rho, inferInstance, inferInstance,
    inferInstance, Representation.ind S.subtype rho, ?_⟩
  rw [hpsi]
  exact inducedCF_eq_representation_character_pf15 S rho

public theorem scalarProduct_representation_char_eq_finrank
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    scalarProduct G sigma.character rho.character =
      (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) := by
  classical
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  calc
    scalarProduct G sigma.character rho.character =
        (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          sigma.character g * rho.character g⁻¹ := by
          unfold scalarProduct
          congr 1
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [representation_character_inv_eq_star_character rho g]
    _ = (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) := by
          simpa using
            (Representation.card_inv_mul_sum_char_mul_char_eq_finrank
              (ρ := rho) (σ := sigma))

public theorem scalarProduct_isBookIrreducible_family
    {G : Type u} {ι : Type v} [Group G] [Finite G] [DecidableEq ι]
    (chi : ι → ClassFunction G)
    (hchi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (chi i))
    (hchi_distinct : Pairwise fun i j => chi i ≠ chi j) :
    ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [IsIrreducibleCharacter] using (hchi_irreducible i).2
  · have hne : chi i ≠ chi j := hchi_distinct hij
    rcases isBookIrreducibleCharacter_representation_witness_irreducible
        (chi i) (hchi_irreducible i) with
      ⟨Vi, _haddi, _hmodi, _hfdi, rhoi, hchari, hirri⟩
    rcases isBookIrreducibleCharacter_representation_witness_irreducible
        (chi j) (hchi_irreducible j) with
      ⟨Vj, _haddj, _hmodj, _hfdj, rhoj, hcharj, hirrj⟩
    have hchars_ne : rhoi.character ≠ rhoj.character := by
      intro hchars
      apply hne
      rw [hchari, hcharj, hchars]
    letI : Representation.IsIrreducible rhoi := hirri
    letI : Representation.IsIrreducible rhoj := hirrj
    simp [hij, hchari, hcharj,
      scalarProduct_representation_char_eq_zero_of_ne rhoi rhoj hchars_ne]

public theorem scalarProduct_isBookIrreducible_ne
    {G : Type u} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsBookIrreducibleCharacter phi)
    (hpsi : IsBookIrreducibleCharacter psi)
    (hne : phi ≠ psi) :
    scalarProduct G phi psi = 0 := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      phi hphi with
    ⟨Vφ, _haddφ, _hmodφ, _hfdφ, rhoφ, hcharφ, hirrφ⟩
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      psi hpsi with
    ⟨Vψ, _haddψ, _hmodψ, _hfdψ, rhoψ, hcharψ, hirrψ⟩
  exact scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    phi psi rhoφ rhoψ hcharφ hcharψ hirrφ hirrψ hne

public theorem scalarProduct_character_character_eq_nat
    {G : Type u} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsCharacter phi) (hpsi : IsCharacter psi) :
    ∃ n : ℕ, scalarProduct G phi psi = (n : ℂ) := by
  rcases hphi with ⟨Vφ, _haddφ, _hmodφ, _hfdφ, rhoφ, hcharφ⟩
  rcases hpsi with ⟨Vψ, _haddψ, _hmodψ, _hfdψ, rhoψ, hcharψ⟩
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap rhoψ rhoφ), ?_⟩
  rw [hcharφ, hcharψ]
  exact scalarProduct_representation_char_eq_finrank rhoψ rhoφ

public theorem scalarProduct_inducedCF_character_eq_nat
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S]
    (phi : ClassFunction S) (psi : ClassFunction G)
    (hphi : IsCharacter phi) (hpsi : IsCharacter psi) :
    ∃ n : ℕ, scalarProduct G (inducedCF S phi) psi = (n : ℂ) := by
  exact scalarProduct_character_character_eq_nat (inducedCF S phi) psi
    (isCharacter_inducedCF_of_isCharacter S phi hphi) hpsi

public theorem scalarProduct_inducedCF_representation_char_eq_nat
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (S : Subgroup G) [Finite S]
    (phi : ClassFunction S) (psi : ClassFunction G)
    (phiRep : Representation ℂ S V) (psiRep : Representation ℂ G W)
    (hphi : phi = phiRep.character)
    (hpsi : psi = psiRep.character) :
    ∃ n : ℕ, scalarProduct G (inducedCF S phi) psi = (n : ℂ) := by
  haveI : FiniteDimensional ℂ (Representation.IndV S.subtype phiRep) :=
    Representation.finiteDimensional_ind S phiRep
  refine ⟨Module.finrank ℂ
      (Representation.IntertwiningMap psiRep (Representation.ind S.subtype phiRep)), ?_⟩
  rw [hphi, hpsi]
  rw [inducedCF_eq_representation_character_pf15 S phiRep]
  exact scalarProduct_representation_char_eq_finrank psiRep
    (Representation.ind S.subtype phiRep)

public theorem nat_weighted_complex_sum_eq_zero_component
    {ι : Type*} [Finite ι] (e n : ι → ℕ)
    (he_pos : ∀ i : ι, 0 < e i) (i : ι)
    (hzero : (∑ j : ι, (e j : ℂ) * (n j : ℂ)) = 0) :
    n i = 0 := by
  classical
  have hcast :
      ((∑ j : ι, e j * n j : ℕ) : ℂ) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_mul] using hzero
  have hsum : ∑ j : ι, e j * n j = 0 := by
    exact_mod_cast hcast
  have hterm_le : e i * n i ≤ ∑ j : ι, e j * n j :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset ι)) (f := fun j : ι => e j * n j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hterm_zero : e i * n i = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [hsum] using hterm_le)
  exact (Nat.mul_eq_zero.mp hterm_zero).resolve_left (Nat.ne_of_gt (he_pos i))

/-! ## Class-function extensionality through irreducible characters -/

@[expose] public noncomputable def toConjClassFunction
    {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) : Representation.ClassFunction G :=
  Representation.classFunctionOfInvariant phi (by
    intro g x
    exact hphi x g)

public theorem toConjClassFunction_apply
    {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) (g : G) :
    toConjClassFunction phi hphi (ConjClasses.mk g) = phi g := rfl

public theorem toConjClassFunction_eq_of_apply
    {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) (Phi : Representation.ClassFunction G)
    (hPhi : ∀ g : G, Phi (ConjClasses.mk g) = phi g) :
    toConjClassFunction phi hphi = Phi := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  exact (toConjClassFunction_apply phi hphi g).trans (hPhi g).symm

public theorem classFunctionInner_toConjClassFunction
    {G : Type*} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsClassFunction phi) (hpsi : IsClassFunction psi) :
    Representation.classFunctionInner
        (toConjClassFunction phi hphi) (toConjClassFunction psi hpsi) =
      scalarProduct G phi psi := by
  classical
  rfl

public theorem representation_classFunctionInner_characterClassFunction
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    Representation.classFunctionInner
        (Representation.characterClassFunction rho)
        (Representation.characterClassFunction sigma) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, rho.character g * sigma.character g⁻¹ := by
  classical
  unfold Representation.classFunctionInner
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [show Representation.characterClassFunction rho (ConjClasses.mk g) =
      rho.character g from rfl]
  rw [show Representation.characterClassFunction sigma (ConjClasses.mk g) =
      sigma.character g from rfl]
  rw [(representation_character_inv_eq_star_character sigma g).symm]

public theorem representation_irreducibleCharacter_witness_irreducible
    {G : Type*} [Group G] [Finite G] (chi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi) :
    ∃ n : ℕ, ∃ rho : Representation ℂ G (Fin n → ℂ),
      chi = Representation.characterClassFunction rho ∧
        Representation.IsIrreducible rho := by
  rcases hchi with ⟨hchar, hirr⟩
  rcases hchar with ⟨n, rho, hchi_eq⟩
  refine ⟨n, rho, hchi_eq, ?_⟩
  apply (Representation.irreducible_iff_character_norm_one (ρ := rho)).2
  simpa [hchi_eq]
    using hirr

public theorem representation_completeFamily_orthonormal
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {chi : ι → Representation.ClassFunction G}
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (i j : ι) :
    Representation.classFunctionInner (chi i) (chi j) =
      if i = j then 1 else 0 := by
  classical
  rcases hchi with ⟨hirr, _hcomplete, hinj⟩
  rcases (hirr i).1 with ⟨ni, rhoi, hchari⟩
  rcases (hirr j).1 with ⟨nj, rhoj, hcharj⟩
  have hirri : Representation.IsIrreducible rhoi := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rhoi)).2
    simpa [hchari] using (hirr i).2
  have hirrj : Representation.IsIrreducible rhoj := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rhoj)).2
    simpa [hcharj] using (hirr j).2
  by_cases hij : i = j
  · subst j
    simpa using (hirr i).2
  · have horth :
        Representation.classFunctionInner
            (Representation.characterClassFunction rhoi)
            (Representation.characterClassFunction rhoj) =
          if Nonempty (Representation.Equiv rhoj rhoi) then 1 else 0 := by
      have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := G)).ne'
      letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
      letI : Representation.IsIrreducible rhoi := hirri
      letI : Representation.IsIrreducible rhoj := hirrj
      rw [representation_classFunctionInner_characterClassFunction]
      simpa using (Representation.char_orthonormal (ρ := rhoi) (σ := rhoj))
    rw [hchari, hcharj, horth]
    have hno : IsEmpty (Representation.Equiv rhoj rhoi) := by
      refine ⟨fun e => hij ?_⟩
      apply hinj
      rw [hchari, hcharj]
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact (congrFun (Representation.char_iso e) g).symm
    have hnone : ¬ Nonempty (Representation.Equiv rhoj rhoi) := by
      intro h
      letI : IsEmpty (Representation.Equiv rhoj rhoi) := hno
      exact isEmptyElim h.some
    simp [hij, hnone]

public theorem representation_classFunctionInner_sum_left
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    (a : ι → ℂ) (phi : ι → Representation.ClassFunction G)
    (psi : Representation.ClassFunction G) :
    Representation.classFunctionInner (∑ i : ι, a i • phi i) psi =
      ∑ i : ι, a i * Representation.classFunctionInner (phi i) psi := by
  classical
  let L : Representation.ClassFunction G →ₗ[ℂ] ℂ :=
    { toFun := fun φ => Representation.classFunctionInner φ psi
      map_add' := by
        intro φ₁ φ₂
        simp [Representation.classFunctionInner, add_mul,
          Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c φ
        simp [Representation.classFunctionInner, Finset.mul_sum,
          mul_assoc, mul_left_comm] }
  calc
    Representation.classFunctionInner (∑ i : ι, a i • phi i) psi = L (∑ i : ι, a i • phi i) := rfl
    _ = ∑ i : ι, a i • L (phi i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [L]
    _ = ∑ i : ι, a i * Representation.classFunctionInner (phi i) psi := by
      rfl

public theorem representation_basis_repr_eq_inner
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {chi : ι → Representation.ClassFunction G}
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (b : Module.Basis ι ℂ (Representation.ClassFunction G))
    (hb : ∀ i, b i = chi i)
    (phi : Representation.ClassFunction G) (i : ι) :
    b.repr phi i = Representation.classFunctionInner phi (chi i) := by
  classical
  have hsum_phi : (∑ j : ι, b.repr phi j • chi j) = phi := by
    calc
      (∑ j : ι, b.repr phi j • chi j) =
          ∑ j : ι, b.repr phi j • b j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [hb j]
      _ = phi := Module.Basis.sum_repr b phi
  have hinner :
      Representation.classFunctionInner phi (chi i) =
        Representation.classFunctionInner (∑ j : ι, b.repr phi j • chi j) (chi i) := by
    rw [hsum_phi]
  have h := congrArg (fun f => Representation.classFunctionInner f (chi i)) hsum_phi
  change Representation.classFunctionInner (∑ j : ι, b.repr phi j • chi j) (chi i) =
    Representation.classFunctionInner phi (chi i) at h
  rw [representation_classFunctionInner_sum_left] at h
  simp [representation_completeFamily_orthonormal hchi] at h
  exact h

public theorem representation_classFunction_eq_of_inner_irreducible
    {G : Type*} [Group G] [Finite G]
    (phi psi : Representation.ClassFunction G)
    (hinner :
      ∀ chi : Representation.ClassFunction G,
        Representation.IsIrreducibleCharacter chi →
          Representation.classFunctionInner phi chi =
            Representation.classFunctionInner psi chi) :
    phi = psi := by
  classical
  rcases Representation.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, chi, hchi, b, hb⟩
  letI : Fintype ι := hι
  apply b.repr.injective
  ext i
  rw [representation_basis_repr_eq_inner hchi b hb phi i]
  rw [representation_basis_repr_eq_inner hchi b hb psi i]
  exact hinner (chi i) (hchi.1 i)

public theorem classFunction_eq_of_inner_irreducible
    {G : Type*} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsClassFunction phi) (hpsi : IsClassFunction psi)
    (hinner :
      ∀ chi : Representation.ClassFunction G,
        Representation.IsIrreducibleCharacter chi →
          Representation.classFunctionInner (toConjClassFunction phi hphi) chi =
            Representation.classFunctionInner (toConjClassFunction psi hpsi) chi) :
    phi = psi := by
  have hbar :
      toConjClassFunction phi hphi = toConjClassFunction psi hpsi :=
    representation_classFunction_eq_of_inner_irreducible
      (toConjClassFunction phi hphi) (toConjClassFunction psi hpsi) hinner
  ext g
  have hg := congrFun hbar (ConjClasses.mk g)
  simpa [toConjClassFunction_apply] using hg

@[expose] public noncomputable def ofConjClassFunction
    {G : Type*} [Group G] (chi : Representation.ClassFunction G) :
    ClassFunction G :=
  fun g => chi (ConjClasses.mk g)

public theorem ofConjClassFunction_apply
    {G : Type*} [Group G] (chi : Representation.ClassFunction G) (g : G) :
    ofConjClassFunction chi g = chi (ConjClasses.mk g) := rfl

public theorem ofConjClassFunction_characterClassFunction
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    ofConjClassFunction (Representation.characterClassFunction rho) =
      rho.character := by
  rfl

public theorem ofConjClassFunction_isClassFunction
    {G : Type*} [Group G] (chi : Representation.ClassFunction G) :
    IsClassFunction (ofConjClassFunction chi) := by
  intro x g
  unfold ofConjClassFunction
  congr 1
  exact (ConjClasses.mk_eq_mk_iff_isConj).2
    ((isConj_iff).2 ⟨x⁻¹, by simp [mul_assoc]⟩)

public theorem toConjClassFunction_ofConjClassFunction
    {G : Type*} [Group G] (chi : Representation.ClassFunction G) :
    toConjClassFunction (ofConjClassFunction chi)
        (ofConjClassFunction_isClassFunction chi) = chi := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  rfl

public theorem scalarProduct_ofConjClassFunction
    {G : Type*} [Group G] [Finite G]
    (phi psi : Representation.ClassFunction G) :
    scalarProduct G (ofConjClassFunction phi) (ofConjClassFunction psi) =
      Representation.classFunctionInner phi psi := by
  symm
  simpa only [toConjClassFunction_ofConjClassFunction] using
    (classFunctionInner_toConjClassFunction
      (ofConjClassFunction phi) (ofConjClassFunction psi)
      (ofConjClassFunction_isClassFunction phi)
      (ofConjClassFunction_isClassFunction psi))

public theorem representation_inner_toConjClassFunction_right
    {G : Type*} [Group G] [Finite G]
    (phi : ClassFunction G) (hphi : IsClassFunction phi)
    (chi : Representation.ClassFunction G) :
    Representation.classFunctionInner (toConjClassFunction phi hphi) chi =
      scalarProduct G phi (ofConjClassFunction chi) := by
  rw [← toConjClassFunction_ofConjClassFunction chi]
  exact classFunctionInner_toConjClassFunction phi (ofConjClassFunction chi)
    hphi (ofConjClassFunction_isClassFunction chi)

@[expose] public noncomputable def uliftRepresentation
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    Representation ℂ G (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (rho g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

public theorem uliftRepresentation_character
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (g : G) :
    (uliftRepresentation (G := G) (V := V) rho).character g = rho.character g := by
  dsimp [uliftRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (rho g) (ULift.moduleEquiv.symm)

public theorem isBookIrreducibleCharacter_of_representation_irreducible
    {G : Type u} [Group G] [Finite G] (chi : Representation.ClassFunction G)
    (hchi : Representation.IsIrreducibleCharacter chi) :
    IsBookIrreducibleCharacter (ofConjClassFunction chi) := by
  rcases hchi with ⟨hchar, hirr⟩
  constructor
  · rcases hchar with ⟨n, rho, hchi_eq⟩
    refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation (G := G) (V := Fin n → ℂ) rho, ?_⟩
    ext g
    rw [hchi_eq]
    exact (uliftRepresentation_character (G := G) (V := Fin n → ℂ) (rho := rho) g).symm
  · rw [IsIrreducibleCharacter]
    simpa [classFunctionInner_toConjClassFunction,
      toConjClassFunction_ofConjClassFunction] using hirr

public theorem isCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {chi : ClassFunction G}
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    IsCharacter chi := by
  rcases hchi with ⟨n, rho, _hirr, hchar⟩
  refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
    uliftRepresentation (G := G) (V := Fin n → ℂ) rho, ?_⟩
  ext g
  simpa [hchar] using
    (uliftRepresentation_character (G := G) (V := Fin n → ℂ) (rho := rho) g).symm

public theorem isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {chi : ClassFunction G}
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    IsBookIrreducibleCharacter chi := by
  rcases hchi with ⟨n, rho, hirr, hchar⟩
  constructor
  · exact isCharacter_of_isIrreducibleCharacterOnGroup
      ⟨n, rho, hirr, hchar⟩
  · rw [IsIrreducibleCharacter]
    simpa [hchar] using
      (Representation.irreducible_iff_character_norm_one (ρ := rho)).1 hirr

public theorem isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
    {G : Type u} [Group G] [Finite G]
    (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    IsIrreducibleCharacterOnGroup chi := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      chi hchi with
    ⟨V, _hadd, _hmod, _hfd, rho, hchar, hirr⟩
  rw [hchar]
  exact isIrreducibleCharacterOnGroup_of_representation rho hirr

public theorem character_irreducible_decomposition_all
    {G : Type u} [Group G] [Finite G]
    (phi : ClassFunction G)
    (hphi_char : IsCharacter phi) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ e : ι → ℕ, ∃ psi : ι → ClassFunction G,
        (∀ i : ι, IsBookIrreducibleCharacter (psi i)) ∧
        Pairwise (fun i j : ι => psi i ≠ psi j) ∧
        phi = weightedFamilySum (fun i => (e i : ℂ)) psi := by
  classical
  have hphi_class : IsClassFunction phi :=
    isCharacter_isClassFunction phi hphi_char
  rcases Representation.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, chi, hchi, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let psi : ι → ClassFunction G :=
    fun i => ofConjClassFunction (chi i)
  have hpsi_book : ∀ i : ι, IsBookIrreducibleCharacter (psi i) := by
    intro i
    exact isBookIrreducibleCharacter_of_representation_irreducible
      (chi i) (hchi.1 i)
  let e : ι → ℕ := fun i => Classical.choose
    (scalarProduct_character_character_eq_nat phi (psi i)
      hphi_char (hpsi_book i).1)
  have he : ∀ i : ι,
      scalarProduct G phi (psi i) = (e i : ℂ) := by
    intro i
    exact Classical.choose_spec
      (scalarProduct_character_character_eq_nat phi (psi i)
        hphi_char (hpsi_book i).1)
  have hphi_sum :
      toConjClassFunction phi hphi_class =
        ∑ i : ι, (e i : ℂ) • chi i := by
    calc
      toConjClassFunction phi hphi_class =
          ∑ i : ι, b.repr (toConjClassFunction phi hphi_class) i • b i := by
            rw [Module.Basis.sum_repr]
      _ = ∑ i : ι, (e i : ℂ) • chi i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hb i]
            congr 1
            rw [representation_basis_repr_eq_inner hchi b hb]
            rw [representation_inner_toConjClassFunction_right]
            exact he i
  refine ⟨ι, hι, Classical.decEq ι, e, psi, hpsi_book, ?_, ?_⟩
  · intro i j hij hpsi_eq
    apply hij
    apply hchi.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hpsi_eq g
  · ext g
    have hg := congrFun hphi_sum (ConjClasses.mk g)
    have hg' : phi g = ∑ i : ι, (e i : ℂ) * psi i g := by
      simpa [psi, toConjClassFunction_apply, ofConjClassFunction] using hg
    have hsum_eq :
        (∑ i : ι, (e i : ℂ) * psi i g) =
          weightedFamilySum (fun i => (e i : ℂ)) psi g := by
      unfold weightedFamilySum
      apply Finset.sum_congr
      · ext i
        simp
      · intro i _hi
        rfl
    exact hg'.trans hsum_eq

public theorem exists_positive_irreducible_decomposition_of_character
    {G : Type u} [Group G] [Finite G]
    (phi : ClassFunction G)
    (hphi_char : IsCharacter phi)
    (hphi_ne : phi ≠ 0) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ e : ι → ℕ, ∃ psi : ι → ClassFunction G, ∃ _i0 : ι,
        (∀ i : ι, 0 < e i) ∧
        (∀ i : ι, IsBookIrreducibleCharacter (psi i)) ∧
        Pairwise (fun i j : ι => psi i ≠ psi j) ∧
        phi = weightedFamilySum (fun i => (e i : ℂ)) psi := by
  classical
  rcases character_irreducible_decomposition_all phi hphi_char with
    ⟨β, hβ, hβdec, e0, psi0, hpsi0, hpair0, hdecomp0⟩
  letI : Fintype β := hβ
  letI : DecidableEq β := hβdec
  have hex : ∃ i : β, e0 i ≠ 0 := by
    by_contra hnone
    have hallzero : ∀ i : β, e0 i = 0 := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    apply hphi_ne
    rw [hdecomp0]
    ext g
    simp [weightedFamilySum, hallzero]
  let s : Finset β := Finset.univ.filter fun i => e0 i ≠ 0
  let γ : Type := {i : β // i ∈ s}
  letI : Fintype γ := inferInstance
  letI : DecidableEq γ := inferInstance
  let e : γ → ℕ := fun i => e0 i.1
  let psi : γ → ClassFunction G := fun i => psi0 i.1
  rcases hex with ⟨i, hi⟩
  let i0 : γ := ⟨i, by simp [s, hi]⟩
  refine ⟨γ, inferInstance, inferInstance, e, psi, i0, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi_mem : i.1 ∈ Finset.univ.filter (fun i : β => e0 i ≠ 0) := by
      simpa [s] using i.2
    exact Nat.pos_of_ne_zero (Finset.mem_filter.mp hi_mem).2
  · intro i
    exact hpsi0 i.1
  · intro i j hij hpsi_eq
    exact hpair0 (fun h => hij (Subtype.ext h)) hpsi_eq
  · rw [hdecomp0]
    ext g
    let f : β → ℂ := fun i => (e0 i : ℂ) * psi0 i g
    have hsub :
        (∑ x : γ, (e x : ℂ) * psi x g) =
          ∑ x ∈ (Finset.univ.filter fun i : β => e0 i ≠ 0), f x := by
      simpa [γ, e, psi, f, s] using
        (Finset.sum_attach
          (s := (Finset.univ.filter fun i : β => e0 i ≠ 0))
          (f := f))
    have hfilter :
        ∑ x ∈ (Finset.univ.filter fun i : β => e0 i ≠ 0), f x =
          ∑ x : β, f x := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : e0 x ≠ 0
      · simp [hx, f]
      · have hx0 : e0 x = 0 := by exact not_not.mp hx
        simp [hx0, f]
    have hsum :
        (∑ x : γ, (e x : ℂ) * psi x g) = ∑ x : β, f x :=
      hsub.trans hfilter
    have hfull :
        (@Finset.sum β ℂ _ (@Finset.univ β (Fintype.ofFinite β)) f) =
          @Finset.sum γ ℂ _ (@Finset.univ γ (Fintype.ofFinite γ))
            (fun x => (e x : ℂ) * psi x g) := by
      have hlocal_beta :
          (∑ x : β, f x) =
            @Finset.sum β ℂ _ (@Finset.univ β (Fintype.ofFinite β)) f := by
        apply Finset.sum_congr
        · ext x
          simp
        · intro x _hx
          rfl
      have hlocal_gamma :
          (∑ x : γ, (e x : ℂ) * psi x g) =
            @Finset.sum γ ℂ _ (@Finset.univ γ (Fintype.ofFinite γ))
              (fun x => (e x : ℂ) * psi x g) := by
        apply Finset.sum_congr
        · ext x
          simp
        · intro x _hx
          rfl
      exact hlocal_beta.symm.trans (hsum.symm.trans hlocal_gamma)
    simpa [weightedFamilySum, e, psi, f] using hfull

public theorem exists_principal_index_of_completeFamily
    {G : Type u} [Group G] [Finite G] {ι : Type} [Fintype ι]
    {chi : ι → Representation.ClassFunction G}
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi) :
    ∃ k : ι, ofConjClassFunction (chi k) = principalCharacter G := by
  classical
  let chi0 : Representation.ClassFunction G :=
    toConjClassFunction (principalCharacter G)
      (by intro x g; simp [principalCharacter])
  have hchi0_irred : Representation.IsIrreducibleCharacter chi0 := by
    let rho : Representation ℂ G (Fin 1 → ℂ) :=
      Representation.trivial ℂ G (Fin 1 → ℂ)
    have hchi0_eq : chi0 = Representation.characterClassFunction rho := by
      refine toConjClassFunction_eq_of_apply
        (principalCharacter G) _ (Representation.characterClassFunction rho) ?_
      intro g
      change rho.character g = principalCharacter G g
      simp [rho, principalCharacter, Representation.character]
    refine ⟨?_, ?_⟩
    · refine ⟨1, rho, hchi0_eq⟩
    · dsimp [chi0]
      rw [classFunctionInner_toConjClassFunction]
      simp [scalarProduct, principalCharacter]
  rcases hchi.2.1 chi0 hchi0_irred with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change ofConjClassFunction (chi k) = ofConjClassFunction chi0
  rw [hk]

/-- A book-facing complete irreducible-character family whose squared degrees
sum to the group order. -/
public theorem exists_bookIrreducibleCharacterFamily_sum_degree_normSq
    {G : Type*} [Group G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ClassFunction G),
      (∀ i, IsBookIrreducibleCharacter (χ i)) ∧
        ∑ i : ι, Complex.normSq (χ i 1) = (Nat.card G : ℝ) := by
  classical
  rcases Representation.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := G) with
    ⟨ι, hι, chi, hchi, hsum⟩
  letI : Fintype ι := hι
  refine ⟨ι, hι, fun i => ofConjClassFunction (chi i), ?_, ?_⟩
  · intro i
    exact isBookIrreducibleCharacter_of_representation_irreducible (chi i) (hchi.1 i)
  · simpa [ofConjClassFunction_apply] using hsum

/-- A book-facing complete irreducible-character family with the principal
character removed from the degree-square sum. -/
public theorem exists_bookIrreducibleCharacterFamily_nonprincipal_sum_degree_normSq
    {G : Type u} [Group G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (χ : ι → ClassFunction G) (i0 : ι),
      (∀ i, IsBookIrreducibleCharacter (χ i)) ∧
        χ i0 = principalCharacter G ∧
        Finset.sum (Finset.univ.erase i0)
            (fun i => Complex.normSq (χ i 1)) =
          (Nat.card G : ℝ) - 1 := by
  classical
  rcases Representation.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := G) with
    ⟨ι, hι, chi, hchi, hsum⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  rcases exists_principal_index_of_completeFamily (G := G)
      (chi := chi) hchi with
    ⟨i0, hi0⟩
  refine ⟨ι, hι, inferInstance, fun i => ofConjClassFunction (chi i),
    i0, ?_, ?_, ?_⟩
  · intro i
    exact isBookIrreducibleCharacter_of_representation_irreducible (chi i) (hchi.1 i)
  · exact hi0
  · have hsum_book :
        ∑ i : ι, Complex.normSq (ofConjClassFunction (chi i) (1 : G)) =
          (Nat.card G : ℝ) := by
      simpa [ofConjClassFunction_apply] using hsum
    have hterm : Complex.normSq (ofConjClassFunction (chi i0) (1 : G)) = 1 := by
      rw [hi0]
      simp [principalCharacter]
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun i => Complex.normSq (ofConjClassFunction (chi i) (1 : G)))
      (Finset.mem_univ i0)
    rw [hsum_book] at hsplit
    have hsplit' :
        Finset.sum (Finset.univ.erase i0)
            (fun i => Complex.normSq (ofConjClassFunction (chi i) (1 : G))) +
            1 =
          (Nat.card G : ℝ) := by
      simpa [hterm] using hsplit
    nlinarith

public theorem isClassFunction_smul
    {G : Type*} [Group G] (c : ℂ) (phi : ClassFunction G)
    (hphi : IsClassFunction phi) :
    IsClassFunction (c • phi) := by
  intro x g
  simp [hphi x g]

public theorem subgroupRestriction_isClassFunction_of_isClassFunction
    {G : Type*} [Group G] (S : Subgroup G) (phi : ClassFunction G)
    (hphi : IsClassFunction phi) :
    IsClassFunction (subgroupRestriction S phi) := by
  intro x g
  exact hphi x g

public theorem scalarProduct_weightedFamilySum_right
    {G ι : Type*} [Finite G] [Finite ι]
    (phi : ClassFunction G) (w : ι → ℂ) (psi : ι → ClassFunction G) :
    scalarProduct G phi (weightedFamilySum w psi) =
      ∑ i : ι, star (w i) * scalarProduct G phi (psi i) := by
  classical
  change scalarProduct G phi (fun g => ∑ i : ι, w i * psi i g) =
    ∑ i : ι, star (w i) * scalarProduct G phi (psi i)
  rw [scalarProduct_fintype_sum_right]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change scalarProduct G phi (w i • psi i) =
    star (w i) * scalarProduct G phi (psi i)
  rw [scalarProduct_smul_right]

public theorem scalarProduct_weightedFamilySum_left
    {G ι : Type*} [Finite G] [Finite ι]
    (w : ι → ℂ) (phi : ι → ClassFunction G) (psi : ClassFunction G) :
    scalarProduct G (weightedFamilySum w phi) psi =
      ∑ i : ι, w i * scalarProduct G (phi i) psi := by
  classical
  unfold weightedFamilySum
  rw [scalarProduct_fintype_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change scalarProduct G (w i • phi i) psi =
    w i * scalarProduct G (phi i) psi
  rw [scalarProduct_smul_left]

/-! ## Virtual-character parity from Proposition (1.1) -/

public theorem isVirtualCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G]
    {χ : ClassFunction G}
    (hχ : Representation.IsVirtualCharacter χ) :
    IsClassFunction χ := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  intro x g
  unfold Representation.virtualCharacterOfRepresentations
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hchar :
      (ρ i).character (x * g * x⁻¹) = (ρ i).character g := by
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ i) g x
  simp [hchar]

public theorem isVirtualCharacter_ofConjClassFunction_of_isCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : Representation.ClassFunction G}
    (hχ : Representation.IsCharacter χ) :
    Representation.IsVirtualCharacter (ofConjClassFunction χ) := by
  classical
  rcases hχ with ⟨n, ρ, hχeq⟩
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => n),
    (fun _ : Fin 1 => ρ), ?_⟩
  ext g
  rw [hχeq]
  change ρ.character g =
    Representation.virtualCharacterOfRepresentations 1
      (fun _ : Fin 1 => (1 : ℤ)) (fun _ : Fin 1 => n)
      (fun _ : Fin 1 => ρ) g
  simp [Representation.virtualCharacterOfRepresentations]

public theorem scalarProduct_isVirtualCharacter_eq_int
    {G : Type u} [Group G] [Finite G]
    {χ ψ : ClassFunction G}
    (hχ : Representation.IsVirtualCharacter χ)
    (hψ : Representation.IsVirtualCharacter ψ) :
    ∃ z : ℤ, scalarProduct G χ ψ = (z : ℂ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  have hpair :
      ∀ i : Fin r, ∀ j : Fin s,
        ∃ k : ℕ, scalarProduct G ((ρ i).character) ((σ j).character) = (k : ℂ) := by
    intro i j
    refine ⟨Module.finrank ℂ (Representation.IntertwiningMap (σ j) (ρ i)), ?_⟩
    simpa using
      (scalarProduct_representation_char_eq_finrank
        (rho := σ j) (sigma := ρ i))
  choose k hk using hpair
  refine ⟨∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j, ?_⟩
  have hcalc :
      scalarProduct G
          (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
          (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) =
        ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := by
    rw [scalarProduct_fintype_sum_left]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [scalarProduct_fintype_sum_right]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    change
      scalarProduct G
          ((m i : ℂ) • (ρ i).character)
          ((m' j : ℂ) • (σ j).character) =
        (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ)
    rw [scalarProduct_smul_left, scalarProduct_smul_right, hk i j]
    simp
    ring
  calc
    scalarProduct G
        (Representation.virtualCharacterOfRepresentations r m n ρ)
        (Representation.virtualCharacterOfRepresentations s m' n' σ)
        =
          scalarProduct G
            (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
            (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) := by
          rfl
    _ = ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := hcalc
    _ = ((∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j : ℤ) : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul, mul_assoc]

public theorem scalarProduct_conjugate_right_of_real_left
    {G : Type*} [Finite G] (φ ψ : ClassFunction G)
    (hφ : φ = conjugateCharacter φ) :
    scalarProduct G φ (conjugateCharacter ψ) =
      star (scalarProduct G φ ψ) := by
  classical
  rw [scalarProduct_star_swap (G := G) (phi := ψ) (psi := φ)]
  unfold scalarProduct conjugateCharacter
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  have hφg : star (φ g) = φ g := by
    simpa [conjugateCharacter] using (congrFun hφ g).symm
  simp [hφg, mul_comm]

public theorem representation_classFunctionInner_star_swap
    {G : Type*} [Group G] [Finite G]
    (φ ψ : Representation.ClassFunction G) :
    star (Representation.classFunctionInner ψ φ) =
      Representation.classFunctionInner φ ψ := by
  classical
  have h := scalarProduct_star_swap (G := G)
    (phi := ofConjClassFunction φ) (psi := ofConjClassFunction ψ)
  simpa [classFunctionInner_toConjClassFunction,
    toConjClassFunction_ofConjClassFunction] using h

public theorem toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : ClassFunction G} (hχclass : IsClassFunction χ)
    (hχ : IsIrreducibleCharacterOnGroup χ) :
    Representation.IsIrreducibleCharacter (toConjClassFunction χ hχclass) := by
  classical
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  have hcf : toConjClassFunction χ hχclass = Representation.characterClassFunction ρ := by
    refine toConjClassFunction_eq_of_apply χ hχclass (Representation.characterClassFunction ρ) ?_
    intro g
    change ρ.character g = χ g
    exact (congrFun hχchar g).symm
  refine ⟨?_, ?_⟩
  · exact ⟨n, ρ, hcf⟩
  · rw [hcf]
    exact (Representation.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr

private theorem even_sum_of_fixedPointFree_involution_finset
    {α : Type*} [DecidableEq α] (s : Finset α) (τ : α → α) (c : α → ℤ)
    (hmem : ∀ x, x ∈ s → τ x ∈ s)
    (hinv : ∀ x, x ∈ s → τ (τ x) = x)
    (hfixed : ∀ x, x ∈ s → τ x ≠ x)
    (hc : ∀ x, x ∈ s → c (τ x) = c x) :
    ∃ z : ℤ, Finset.sum s c = 2 * z := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ t : Finset α, t.card = n →
      (∀ x, x ∈ t → τ x ∈ t) →
      (∀ x, x ∈ t → τ (τ x) = x) →
      (∀ x, x ∈ t → τ x ≠ x) →
      (∀ x, x ∈ t → c (τ x) = c x) →
      ∃ z : ℤ, Finset.sum t c = 2 * z
  have hP : P s.card := by
    refine Nat.strong_induction_on (p := P) s.card ?_
    intro n ih t ht_card hmem hinv hfixed hc
    by_cases ht_empty : t = ∅
    · subst t
      refine ⟨0, by simp⟩
    · have ht_nonempty : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_empty
      rcases ht_nonempty with ⟨a, ha⟩
      let b := τ a
      have hb : b ∈ t := hmem a ha
      have hba : b ≠ a := hfixed a ha
      let t' := (t.erase a).erase b
      have ht'_sub : ∀ x, x ∈ t' → x ∈ t := by
        intro x hx
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
      have hmem' : ∀ x, x ∈ t' → τ x ∈ t' := by
        intro x hx
        have hx_t : x ∈ t := ht'_sub x hx
        have hx_ne_b : x ≠ b := (Finset.mem_erase.mp hx).1
        have hx_ne_a : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        have htx_t : τ x ∈ t := hmem x hx_t
        have htx_ne_a : τ x ≠ a := by
          intro hxa
          have hx_eq_b : x = b := by
            calc
              x = τ (τ x) := (hinv x hx_t).symm
              _ = τ a := by rw [hxa]
              _ = b := rfl
          exact hx_ne_b hx_eq_b
        have htx_ne_b : τ x ≠ b := by
          intro hxb
          have hx_eq_a : x = a := by
            calc
              x = τ (τ x) := (hinv x hx_t).symm
              _ = τ b := by rw [hxb]
              _ = a := hinv a ha
          exact hx_ne_a hx_eq_a
        exact Finset.mem_erase.mpr
          ⟨htx_ne_b, Finset.mem_erase.mpr ⟨htx_ne_a, htx_t⟩⟩
      have hinv' : ∀ x, x ∈ t' → τ (τ x) = x := by
        intro x hx
        exact hinv x (ht'_sub x hx)
      have hfixed' : ∀ x, x ∈ t' → τ x ≠ x := by
        intro x hx
        exact hfixed x (ht'_sub x hx)
      have hc' : ∀ x, x ∈ t' → c (τ x) = c x := by
        intro x hx
        exact hc x (ht'_sub x hx)
      have hb_erase : b ∈ t.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
      have hcard_lt : t'.card < n := by
        rw [← ht_card]
        exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem hb_erase)
          (Finset.card_erase_le (s := t) (a := a))
      rcases ih t'.card hcard_lt t' rfl hmem' hinv' hfixed' hc' with ⟨z, hz⟩
      refine ⟨c a + z, ?_⟩
      have hsum_a := Finset.sum_erase_add t c ha
      have hsum_b := Finset.sum_erase_add (t.erase a) c hb_erase
      have hcb : c b = c a := hc a ha
      calc
        Finset.sum t c = Finset.sum (t.erase a) c + c a := hsum_a.symm
        _ = (Finset.sum t' c + c b) + c a := by rw [hsum_b.symm]
        _ = 2 * (c a + z) := by rw [hcb, hz]; ring
  exact hP s rfl hmem hinv hfixed hc

public theorem scalarProduct_real_virtualCharacters_eq_one_add_two_mul
    {G : Type u} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {χ ψ : ClassFunction G}
    (hχv : Representation.IsVirtualCharacter χ)
    (hψv : Representation.IsVirtualCharacter ψ)
    (hχreal : χ = conjugateCharacter χ)
    (hψreal : ψ = conjugateCharacter ψ)
    (hχprincipal : scalarProduct G χ (principalCharacter G) = 1)
    (hψprincipal : scalarProduct G ψ (principalCharacter G) = 1) :
    ∃ z : ℤ, scalarProduct G χ ψ = (1 : ℂ) + 2 * (z : ℂ) := by
  classical
  have hχclass : IsClassFunction χ := isVirtualCharacter_isClassFunction hχv
  have hψclass : IsClassFunction ψ := isVirtualCharacter_isClassFunction hψv
  rcases Representation.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, ξ, hξ, bas, hbas⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let μ : ι → ClassFunction G := fun i => ofConjClassFunction (ξ i)
  have hμv : ∀ i, Representation.IsVirtualCharacter (μ i) := by
    intro i
    exact isVirtualCharacter_ofConjClassFunction_of_isCharacter (hξ.1 i).1
  let a : ι → ℤ := fun i =>
    Classical.choose (scalarProduct_isVirtualCharacter_eq_int hχv (hμv i))
  let bcoef : ι → ℤ := fun i =>
    Classical.choose (scalarProduct_isVirtualCharacter_eq_int hψv (hμv i))
  have ha_spec : ∀ i, scalarProduct G χ (μ i) = (a i : ℂ) := by
    intro i
    exact Classical.choose_spec (scalarProduct_isVirtualCharacter_eq_int hχv (hμv i))
  have hb_spec : ∀ i, scalarProduct G ψ (μ i) = (bcoef i : ℂ) := by
    intro i
    exact Classical.choose_spec (scalarProduct_isVirtualCharacter_eq_int hψv (hμv i))
  let Φ : Representation.ClassFunction G := toConjClassFunction χ hχclass
  let Ψ : Representation.ClassFunction G := toConjClassFunction ψ hψclass
  have hχsum : Φ = ∑ i : ι, (a i : ℂ) • ξ i := by
    calc
      Φ = ∑ i : ι, bas.repr Φ i • bas i := by
        rw [Module.Basis.sum_repr]
      _ = ∑ i : ι, (a i : ℂ) • ξ i := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [hbas i]
        congr 1
        rw [representation_basis_repr_eq_inner hξ bas hbas]
        rw [representation_inner_toConjClassFunction_right]
        exact ha_spec i
  have hinner_right : ∀ i,
      Representation.classFunctionInner (ξ i) Ψ = (bcoef i : ℂ) := by
    intro i
    calc
      Representation.classFunctionInner (ξ i) Ψ =
          star (Representation.classFunctionInner Ψ (ξ i)) := by
            exact (representation_classFunctionInner_star_swap (G := G) (ξ i) Ψ).symm
      _ = star (scalarProduct G ψ (μ i)) := by
            rw [representation_inner_toConjClassFunction_right]
      _ = (bcoef i : ℂ) := by
            rw [hb_spec i]
            simp
  have hsp : scalarProduct G χ ψ =
      ∑ i : ι, (a i : ℂ) * (bcoef i : ℂ) := by
    calc
      scalarProduct G χ ψ = Representation.classFunctionInner Φ Ψ := by
        rw [← classFunctionInner_toConjClassFunction χ ψ hχclass hψclass]
      _ = Representation.classFunctionInner (∑ i : ι, (a i : ℂ) • ξ i) Ψ := by
        rw [hχsum]
      _ = ∑ i : ι, (a i : ℂ) * Representation.classFunctionInner (ξ i) Ψ := by
        rw [representation_classFunctionInner_sum_left]
      _ = ∑ i : ι, (a i : ℂ) * (bcoef i : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [hinner_right i]
  have hbarClass : ∀ i, IsClassFunction (conjugateCharacter (μ i)) := by
    intro i x g
    have hμclass := ofConjClassFunction_isClassFunction (ξ i)
    change star ((ofConjClassFunction (ξ i)) (x * g * x⁻¹)) =
      star ((ofConjClassFunction (ξ i)) g)
    rw [hμclass x g]
  have hbarIrr : ∀ i,
      Representation.IsIrreducibleCharacter
        (toConjClassFunction (conjugateCharacter (μ i)) (hbarClass i)) := by
    intro i
    have hbook : IsBookIrreducibleCharacter (μ i) :=
      isBookIrreducibleCharacter_of_representation_irreducible (ξ i) (hξ.1 i)
    have hgroup : IsIrreducibleCharacterOnGroup (μ i) :=
      isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter (μ i) hbook
    exact toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (hbarClass i) (isIrreducibleCharacterOnGroup_conjugateCharacter hgroup)
  let τ : ι → ι := fun i => Classical.choose (hξ.2.1 _ (hbarIrr i))
  have hτ_spec : ∀ i,
      ξ (τ i) = toConjClassFunction (conjugateCharacter (μ i)) (hbarClass i) := by
    intro i
    exact Classical.choose_spec (hξ.2.1 _ (hbarIrr i))
  have hμτ : ∀ i, μ (τ i) = conjugateCharacter (μ i) := by
    intro i
    ext g
    have h := congrFun (hτ_spec i) (ConjClasses.mk g)
    simpa [μ, toConjClassFunction_apply] using h
  have hofConj_inj : Function.Injective
      (fun η : Representation.ClassFunction G => ofConjClassFunction η) := by
    intro η θ hηθ
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hηθ g
  have hττ : ∀ i, τ (τ i) = i := by
    intro i
    apply hξ.2.2
    apply hofConj_inj
    calc
      μ (τ (τ i)) = conjugateCharacter (μ (τ i)) := hμτ (τ i)
      _ = conjugateCharacter (conjugateCharacter (μ i)) := by rw [hμτ i]
      _ = μ i := by ext g; simp [conjugateCharacter]
  rcases exists_principal_index_of_completeFamily (G := G) (chi := ξ) hξ with
    ⟨i0, hi0⟩
  have hμi0 : μ i0 = principalCharacter G := by
    simpa [μ] using hi0
  have hτ0 : τ i0 = i0 := by
    apply hξ.2.2
    apply hofConj_inj
    calc
      μ (τ i0) = conjugateCharacter (μ i0) := hμτ i0
      _ = μ i0 := by rw [hμi0, conjugateCharacter_principalCharacter]
  have ha0C : (a i0 : ℂ) = 1 := by
    rw [← ha_spec i0, hμi0, hχprincipal]
  have hb0C : (bcoef i0 : ℂ) = 1 := by
    rw [← hb_spec i0, hμi0, hψprincipal]
  have ha0 : a i0 = 1 := by exact_mod_cast ha0C
  have hb0 : bcoef i0 = 1 := by exact_mod_cast hb0C
  have haτ : ∀ i, a (τ i) = a i := by
    intro i
    have hcalc : scalarProduct G χ (μ (τ i)) =
        star (scalarProduct G χ (μ i)) := by
      rw [hμτ i]
      exact scalarProduct_conjugate_right_of_real_left χ (μ i) hχreal
    have hC : (a (τ i) : ℂ) = (a i : ℂ) := by
      rw [← ha_spec (τ i), hcalc, ha_spec i]
      simp
    exact_mod_cast hC
  have hbτ : ∀ i, bcoef (τ i) = bcoef i := by
    intro i
    have hcalc : scalarProduct G ψ (μ (τ i)) =
        star (scalarProduct G ψ (μ i)) := by
      rw [hμτ i]
      exact scalarProduct_conjugate_right_of_real_left ψ (μ i) hψreal
    have hC : (bcoef (τ i) : ℂ) = (bcoef i : ℂ) := by
      rw [← hb_spec (τ i), hcalc, hb_spec i]
      simp
    exact_mod_cast hC
  have hno_fixed : ∀ i, i ≠ i0 → τ i ≠ i := by
    intro i hi_ne hfix
    rcases representation_irreducibleCharacter_witness_irreducible (ξ i) (hξ.1 i) with
      ⟨n, ρ, hξi, hρirr⟩
    have hμρ : μ i = ρ.character := by
      ext g
      change (ofConjClassFunction (ξ i)) g = ρ.character g
      rw [hξi]
      change Representation.characterClassFunction ρ (ConjClasses.mk g) = ρ.character g
      rfl
    have hne_principal : ρ.character ≠ principalCharacter G := by
      intro hρprin
      apply hi_ne
      apply hξ.2.2
      apply hofConj_inj
      calc
        μ i = ρ.character := hμρ
        _ = principalCharacter G := hρprin
        _ = μ i0 := hμi0.symm
    have hself : μ i = conjugateCharacter (μ i) := by
      rw [← hμτ i, hfix]
    have hfixedρ : ρ.character = conjugateCharacter ρ.character := by
      calc
        ρ.character = μ i := hμρ.symm
        _ = conjugateCharacter (μ i) := hself
        _ = conjugateCharacter ρ.character := by rw [hμρ]
    exact (proposition_1_1 hodd ρ hρirr hne_principal) hfixedρ
  let s : Finset ι := (Finset.univ : Finset ι).erase i0
  let c : ι → ℤ := fun i => a i * bcoef i
  have hτ_mem_s : ∀ i, i ∈ s → τ i ∈ s := by
    intro i hi
    have hi_ne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hτi0
    apply hi_ne
    calc
      i = τ (τ i) := (hττ i).symm
      _ = τ i0 := by rw [hτi0]
      _ = i0 := hτ0
  have hτ_fixed_s : ∀ i, i ∈ s → τ i ≠ i := by
    intro i hi
    exact hno_fixed i (Finset.mem_erase.mp hi).1
  have hcτ : ∀ i, i ∈ s → c (τ i) = c i := by
    intro i _hi
    simp [c, haτ i, hbτ i]
  rcases even_sum_of_fixedPointFree_involution_finset s τ c hτ_mem_s
      (fun i _hi => hττ i) hτ_fixed_s hcτ with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hsum_split : Finset.sum (Finset.univ : Finset ι) c = 1 + 2 * z := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset ι) c (Finset.mem_univ i0)
    calc
      Finset.sum (Finset.univ : Finset ι) c = Finset.sum s c + c i0 := hsum.symm
      _ = 2 * z + 1 := by
        rw [hz]
        change 2 * z + a i0 * bcoef i0 = 2 * z + 1
        rw [ha0, hb0]
        ring
      _ = 1 + 2 * z := by ring
  calc
    scalarProduct G χ ψ = ∑ i : ι, (a i : ℂ) * (bcoef i : ℂ) := hsp
    _ = ((Finset.sum (Finset.univ : Finset ι) c : ℤ) : ℂ) := by
      simp [c, Int.cast_sum, Int.cast_mul]
    _ = (1 : ℂ) + 2 * (z : ℂ) := by
      rw [hsum_split]
      norm_num

/-! ## Book-facing subgroup notation for Proposition (1.7) -/

@[expose] public def subgroupOfClassFunction
    {G : Type*} [Group G] {H T : Subgroup G}
    (theta : ClassFunction H) : ClassFunction (H.subgroupOf T) :=
  fun h => theta ⟨(h : T), h.2⟩

public theorem subgroupOfClassFunction_apply
    {G : Type*} [Group G] {H T : Subgroup G}
    (theta : ClassFunction H) (h : H.subgroupOf T) :
    subgroupOfClassFunction theta h = theta ⟨(h : T), h.2⟩ := rfl

public theorem subgroupOf_normal_of_normal
    {G : Type*} [Group G] (H T : Subgroup G) [hH : H.Normal] :
    (H.subgroupOf T).Normal := by
  exact Subgroup.Normal.subgroupOf (G := G) (hH := hH) T

public theorem proposition_1_7_inertia_contains_H
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (hclass : IsClassFunction theta) :
    H ≤ inertiaSubgroup H theta := by
  intro x hx
  change conjugateOnNormal H theta x = theta
  funext h
  simpa [conjugateOnNormal] using hclass ⟨x, hx⟩ h

public theorem conjugateOnNormal_subgroupOfClassFunction_of_inertia
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H)
    (t : inertiaSubgroup H theta) :
    conjugateOnNormal (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupOfClassFunction theta) t =
      subgroupOfClassFunction theta := by
  haveI : (H.subgroupOf (inertiaSubgroup H theta)).Normal :=
    subgroupOf_normal_of_normal H (inertiaSubgroup H theta)
  ext h
  have ht := congrFun t.2 ⟨(h : inertiaSubgroup H theta), h.2⟩
  simpa [conjugateOnNormal, subgroupOfClassFunction, mul_assoc] using ht

public theorem conjugateOrbitConj_subgroupOfClassFunction_of_inertia
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H)
    (o : conjugateOrbitIndex
        (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupOfClassFunction theta)) :
    conjugateOrbitConj
        (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupOfClassFunction theta) o =
      subgroupOfClassFunction theta := by
  haveI : (H.subgroupOf (inertiaSubgroup H theta)).Normal :=
    subgroupOf_normal_of_normal H (inertiaSubgroup H theta)
  refine Quotient.inductionOn o ?_
  intro t
  exact conjugateOnNormal_subgroupOfClassFunction_of_inertia H theta t

public theorem conjugateOrbitConj_subgroupOfClassFunction_of_inertia_rep
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H)
    (thetaRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (htheta :
      subgroupOfClassFunction theta = thetaRep.character)
    (o : conjugateOrbitIndex
        (H.subgroupOf (inertiaSubgroup H theta))
        thetaRep.character) :
    conjugateOrbitConj
        (H.subgroupOf (inertiaSubgroup H theta))
        thetaRep.character o =
      thetaRep.character := by
  haveI : (H.subgroupOf (inertiaSubgroup H theta)).Normal :=
    subgroupOf_normal_of_normal H (inertiaSubgroup H theta)
  refine Quotient.inductionOn o ?_
  intro t
  change conjugateOnNormal
      (H.subgroupOf (inertiaSubgroup H theta))
      thetaRep.character t = thetaRep.character
  rw [← htheta]
  exact conjugateOnNormal_subgroupOfClassFunction_of_inertia H theta t

@[expose] public noncomputable def thetaOnInertiaSubgroup
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) :
    ClassFunction (H.subgroupOf (inertiaSubgroup H theta)) :=
  subgroupOfClassFunction theta

@[expose] public noncomputable def inducedToInertia
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) :
    ClassFunction (inertiaSubgroup H theta) :=
  inducedCF (H.subgroupOf (inertiaSubgroup H theta))
    (thetaOnInertiaSubgroup H theta)

/-! ## Honest helper lemmas -/

public lemma weightedFamilySum_eq_const_smul_familySum
    {G ι : Type*} [Finite ι] (w : ι → ℂ) (Phi : ι → ClassFunction G) (c : ℂ)
    (hw : ∀ i : ι, w i = c) :
    weightedFamilySum w Phi = c • familySum Phi := by
  funext g
  simp [weightedFamilySum, familySum, hw, Finset.mul_sum]

public lemma weightedFamilySum_nat_eq_const_smul_familySum
    {G ι : Type*} [Finite ι] (e : ι → ℕ) (Phi : ι → ClassFunction G) (m : ℕ)
    (he : ∀ i : ι, e i = m) :
    weightedFamilySum (fun i => (e i : ℂ)) Phi = (m : ℂ) • familySum Phi := by
  apply weightedFamilySum_eq_const_smul_familySum
  intro i
  exact_mod_cast he i

lemma familySum_eq_weightedFamilySum_one
    {G ι : Type*} [Finite ι] (Phi : ι → ClassFunction G) :
    familySum Phi = weightedFamilySum (fun _ : ι => (1 : ℂ)) Phi := by
  funext g
  simp [familySum, weightedFamilySum]

lemma weightedFamilySum_one
    {G ι : Type*} [Finite ι] (Phi : ι → ClassFunction G) :
    weightedFamilySum (fun _ : ι => (1 : ℂ)) Phi = familySum Phi := by
  symm
  exact familySum_eq_weightedFamilySum_one Phi

lemma degree_smul
    {G : Type*} [One G] (c : ℂ) (phi : ClassFunction G) :
    degree (c • phi) = c * degree phi := by
  simp [degree]

lemma degree_familySum
    {G ι : Type*} [One G] [Finite ι] (Phi : ι → ClassFunction G) :
    degree (familySum Phi) = ∑ i : ι, degree (Phi i) := by
  simp [degree, familySum]

/-! ## Linearity of induction on finite sums -/

@[expose] public noncomputable def inducedCFLinear
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [Finite S] :
    ClassFunction S →ₗ[ℂ] ClassFunction G where
  toFun := inducedCF S
  map_add' phi psi := inducedClassFunction_add S phi psi
  map_smul' z phi := inducedClassFunction_smul S z phi

public theorem inducedCFLinear_apply
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [Finite S]
    (phi : ClassFunction S) :
    inducedCFLinear S phi = inducedCF S phi := rfl

public theorem inducedCF_familySum
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (S : Subgroup G) [Finite S] (Phi : ι → ClassFunction S) :
    inducedCF S (familySum Phi) = familySum (fun i => inducedCF S (Phi i)) := by
  classical
  let L := inducedCFLinear S
  have hdomain : familySum Phi = ∑ i : ι, Phi i := by
    ext s
    simp [familySum]
  have hcodomain : (∑ i : ι, L (Phi i)) = familySum (fun i => inducedCF S (Phi i)) := by
    ext g
    simp [familySum, L, inducedCFLinear]
  calc
    inducedCF S (familySum Phi) = L (∑ i : ι, Phi i) := by
      rw [hdomain]
      rfl
    _ = ∑ i : ι, L (Phi i) := by
      exact map_sum L (fun i => Phi i) Finset.univ
    _ = familySum (fun i => inducedCF S (Phi i)) := hcodomain

public theorem inducedCF_weightedFamilySum
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (S : Subgroup G) [Finite S] (w : ι → ℂ) (Phi : ι → ClassFunction S) :
    inducedCF S (weightedFamilySum w Phi) =
      weightedFamilySum w (fun i => inducedCF S (Phi i)) := by
  classical
  let L := inducedCFLinear S
  have hdomain : weightedFamilySum w Phi = ∑ i : ι, w i • Phi i := by
    ext s
    simp [weightedFamilySum]
  have hcodomain :
      (∑ i : ι, L (w i • Phi i)) =
        weightedFamilySum w (fun i => inducedCF S (Phi i)) := by
    ext g
    simp [weightedFamilySum, L, inducedCFLinear]
  calc
    inducedCF S (weightedFamilySum w Phi) = L (∑ i : ι, w i • Phi i) := by
      rw [hdomain]
      rfl
    _ = ∑ i : ι, L (w i • Phi i) := by
      exact map_sum L (fun i => w i • Phi i) Finset.univ
    _ = weightedFamilySum w (fun i => inducedCF S (Phi i)) := hcodomain

public theorem inducedCF_trans
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (theta : ClassFunction H) :
    inducedCF T (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) =
      inducedCF H theta := by
  classical
  funext g
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  let F : G → ℂ := fun y =>
    if hy : y * g * y⁻¹ ∈ H then theta ⟨y * g * y⁻¹, hy⟩ else 0
  have hcardT_ne : (Nat.card T : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := T)).ne'
  have hcardH_ne : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hcardHsub : Nat.card Hsub = Nat.card H := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHT).toEquiv
  have hterm_mem_iff :
      ∀ (x : G) (t : T) (hxT : x * g * x⁻¹ ∈ T),
        ((t * (⟨x * g * x⁻¹, hxT⟩ : T) * t⁻¹ : T) ∈ Hsub) ↔
          (t : G) * x * g * x⁻¹ * (t : G)⁻¹ ∈ H := by
    intro x t hxT
    change ((t : G) * (x * g * x⁻¹) * (t : G)⁻¹ ∈ H) ↔
      (t : G) * x * g * x⁻¹ * (t : G)⁻¹ ∈ H
    simp [mul_assoc]
  have hinner :
      ∀ x : G,
        (if hxT : x * g * x⁻¹ ∈ T then
            inducedCF Hsub thetaSub ⟨x * g * x⁻¹, hxT⟩
          else 0) =
          (Nat.card Hsub : ℂ)⁻¹ * ∑ t : T, F ((t : G) * x) := by
    intro x
    by_cases hxT : x * g * x⁻¹ ∈ T
    · rw [dif_pos hxT]
      unfold inducedCF inducedClassFunction
      congr 1
      refine Finset.sum_congr ?_ ?_
      · ext t
        simp
      intro t _ht
      let a : T := ⟨x * g * x⁻¹, hxT⟩
      change
        (if h : (t * a * t⁻¹ : T) ∈ Hsub then
            thetaSub ⟨t * a * t⁻¹, h⟩
          else 0) =
          F ((t : G) * x)
      by_cases hleft : (t * a * t⁻¹ : T) ∈ Hsub
      · rw [dif_pos hleft]
        dsimp [F]
        have hright : ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ H := by
          have hraw := (hterm_mem_iff x t hxT).mp hleft
          simpa [a, mul_assoc] using hraw
        rw [dif_pos hright]
        simp [thetaSub, subgroupOfClassFunction, a, mul_assoc]
      · rw [dif_neg hleft]
        dsimp [F]
        have hright : ¬ ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ H := by
          intro hmem
          apply hleft
          apply (hterm_mem_iff x t hxT).mpr
          simpa [a, mul_assoc] using hmem
        rw [dif_neg hright]
    · rw [dif_neg hxT]
      have hzero : ∀ t : T, F ((t : G) * x) = 0 := by
        intro t
        dsimp [F]
        by_cases htH : ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ H
        · exfalso
          apply hxT
          have htT : ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ T := hHT htH
          have hback :
              (t : G)⁻¹ * (((t : G) * x) * g * ((t : G) * x)⁻¹) * (t : G) ∈ T :=
            T.mul_mem (T.mul_mem (T.inv_mem t.2) htT) t.2
          simpa [mul_assoc] using hback
        · have htH' : ¬ (t : G) * x * g * (x⁻¹ * (t : G)⁻¹) ∈ H := by
            simpa [mul_assoc] using htH
          simp [htH']
      simp [hzero]
  have hsumPairs :
      (∑ x : G, ∑ t : T, F ((t : G) * x)) =
        (Nat.card T : ℂ) * ∑ y : G, F y := by
    calc
      (∑ x : G, ∑ t : T, F ((t : G) * x)) =
          ∑ t : T, ∑ x : G, F ((t : G) * x) := by
            rw [Finset.sum_comm]
      _ = ∑ _t : T, ∑ y : G, F y := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            exact Equiv.sum_comp (Equiv.mulLeft (t : G)) F
      _ = (Nat.card T : ℂ) * ∑ y : G, F y := by
            simp [Finset.card_univ]
  calc
    inducedCF T (inducedCF Hsub thetaSub) g =
        (Nat.card T : ℂ)⁻¹ *
          ∑ x : G,
            (if hxT : x * g * x⁻¹ ∈ T then
              inducedCF Hsub thetaSub ⟨x * g * x⁻¹, hxT⟩
            else 0) := by
          rfl
    _ = (Nat.card T : ℂ)⁻¹ *
        ∑ x : G, (Nat.card Hsub : ℂ)⁻¹ * ∑ t : T, F ((t : G) * x) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [hinner x]
    _ = (Nat.card T : ℂ)⁻¹ *
        ((Nat.card Hsub : ℂ)⁻¹ * ∑ x : G, ∑ t : T, F ((t : G) * x)) := by
          congr 1
          rw [Finset.mul_sum]
    _ = (Nat.card T : ℂ)⁻¹ *
        ((Nat.card H : ℂ)⁻¹ * ((Nat.card T : ℂ) * ∑ y : G, F y)) := by
          rw [hcardHsub, hsumPairs]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ y : G, F y := by
          field_simp [hcardT_ne, hcardH_ne]
    _ = inducedCF H theta g := by
          rfl

public theorem scalarProduct_inducedCF_left
    {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) [Finite T]
    (psi : ClassFunction T) (chi : ClassFunction G)
    (hchi : IsClassFunction chi) :
    scalarProduct G (inducedCF T psi) chi =
      scalarProduct T psi (subgroupRestriction T chi) :=
  inducedClassFunction_frobenius_general T psi chi hchi

public theorem scalarProduct_inducedCF_inducedCF_left
    {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) [Finite T]
    (psi phi : ClassFunction T) :
    scalarProduct G (inducedCF T psi) (inducedCF T phi) =
      scalarProduct T psi (subgroupRestriction T (inducedCF T phi)) :=
  scalarProduct_inducedCF_left T psi (inducedCF T phi)
    (inducedCF_isClassFunction T phi)

public theorem proposition_1_7_a_decomposition_from_induction
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (T : Subgroup G) [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T)
    (indTHtheta : ClassFunction T) (indGHtheta : ClassFunction G)
    (htrans : indGHtheta = inducedCF T indTHtheta)
    (hdecompT : indTHtheta = weightedFamilySum (fun i => (e i : ℂ)) psi) :
    indGHtheta =
      weightedFamilySum (fun i => (e i : ℂ)) (fun i => inducedCF T (psi i)) := by
  rw [htrans, hdecompT, inducedCF_weightedFamilySum]

public theorem proposition_1_7_a_decomposition_from_subgroup
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi) :
    inducedCF H theta =
      weightedFamilySum (fun i => (e i : ℂ)) (fun i => inducedCF T (psi i)) := by
  rw [← inducedCF_trans H T hHT theta, hdecompT, inducedCF_weightedFamilySum]

/-! ## Degree-counting core for Proposition (1.7)(b) -/

public theorem degree_subgroupOfClassFunction
    {G : Type*} [Group G] {H T : Subgroup G}
    (theta : ClassFunction H) :
    degree (subgroupOfClassFunction (T := T) theta) = degree theta := by
  rfl

public theorem degree_inducedToSubgroup
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T] (theta : ClassFunction H) :
    degree (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) =
      (Subgroup.index (H.subgroupOf T) : ℂ) * degree theta := by
  rw [degree_inducedClassFunction, degree_subgroupOfClassFunction]

public theorem degree_inducedFromSubgroup_constituent
    {G H ι : Type*} [Group G] [Finite G] [One H] [Finite ι]
    (T : Subgroup G) [Finite T] (e : ℕ)
    (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta) :
    ∀ i : ι,
      degree (inducedCF T (psi i)) =
        (Subgroup.index T * e : ℂ) * degree theta := by
  intro i
  rw [degree_inducedClassFunction, hpsiDegree i]
  ring

public theorem proposition_1_7_b_degree_count_complex
    {H T ι : Type*} [One H] [One T] [Finite ι]
    (e : ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (indTHtheta : ClassFunction T) (tIndexH : ℕ)
    (hIndDegree : degree indTHtheta = (tIndexH : ℂ) * degree theta)
    (hdecomp : indTHtheta = (e : ℂ) • familySum psi)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta)
    (htheta_ne_zero : degree theta ≠ 0) :
    (Nat.card ι : ℂ) * (e : ℂ)^2 = (tIndexH : ℂ) := by
  have hdegree :
      (tIndexH : ℂ) * degree theta =
        ((Nat.card ι : ℂ) * (e : ℂ)^2) * degree theta := by
    calc
      (tIndexH : ℂ) * degree theta = degree indTHtheta := hIndDegree.symm
      _ = degree ((e : ℂ) • familySum psi) := by rw [hdecomp]
      _ = (e : ℂ) * degree (familySum psi) := degree_smul (e : ℂ) (familySum psi)
      _ = (e : ℂ) * ∑ i : ι, degree (psi i) := by rw [degree_familySum]
      _ = (e : ℂ) * ∑ _i : ι, (e : ℂ) * degree theta := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [hpsiDegree i]
      _ = ((Nat.card ι : ℂ) * (e : ℂ)^2) * degree theta := by
        simp [Finset.card_univ]
        ring
  exact (mul_right_cancel₀ htheta_ne_zero hdegree).symm

public theorem proposition_1_7_b_degree_count_nat
    {n e m : ℕ}
    (hcountC : (n : ℂ) * (e : ℂ)^2 = (m : ℂ)) :
    n * e^2 = m := by
  exact_mod_cast hcountC

public theorem proposition_1_7_b_degree_count
    {H T ι : Type*} [One H] [One T] [Finite ι]
    (e : ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (indTHtheta : ClassFunction T) (tIndexH : ℕ)
    (hIndDegree : degree indTHtheta = (tIndexH : ℂ) * degree theta)
    (hdecomp : indTHtheta = (e : ℂ) • familySum psi)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta)
    (htheta_ne_zero : degree theta ≠ 0) :
    Nat.card ι * e^2 = tIndexH :=
  proposition_1_7_b_degree_count_nat
    (proposition_1_7_b_degree_count_complex e psi theta indTHtheta tIndexH
      hIndDegree hdecomp hpsiDegree htheta_ne_zero)

public theorem proposition_1_7_b_degree_count_from_subgroup
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hdecomp :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        (e : ℂ) • familySum psi)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta)
    (htheta_ne_zero : degree theta ≠ 0) :
    Nat.card ι * e^2 = Subgroup.index (H.subgroupOf T) :=
  proposition_1_7_b_degree_count e psi theta
    (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta))
    (Subgroup.index (H.subgroupOf T))
    (degree_inducedToSubgroup H T theta)
    hdecomp hpsiDegree htheta_ne_zero

public theorem proposition_1_7_common_multiplicity_eq_one
    {ι : Type*} (e : ι → ℕ) (i0 : ι)
    (heq : ∀ i : ι, e i = e i0)
    (hexistsOne : ∃ i : ι, e i = 1) :
    e i0 = 1 := by
  rcases hexistsOne with ⟨i, hi⟩
  rw [← heq i, hi]

public theorem scalarProduct_weightedFamilySum_left_orthonormal
    {G ι : Type*} [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℂ) (chi : ι → ClassFunction G)
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (j : ι) :
    scalarProduct G (weightedFamilySum w chi) (chi j) = w j := by
  classical
  have hsum :
      weightedFamilySum w chi = fun g => ∑ i : ι, (w i • chi i) g := by
    ext g
    simp [weightedFamilySum]
  rw [hsum, scalarProduct_fintype_sum_left]
  calc
    (∑ i : ι, scalarProduct G (w i • chi i) (chi j)) =
        ∑ i : ι, w i * scalarProduct G (chi i) (chi j) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [scalarProduct_smul_left]
    _ = ∑ i : ι, if i = j then w i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [horth i j]
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
    _ = w j := by
          simp

public theorem proposition_1_7_multiplicity_from_decomposition
    {G ι : Type*} [Finite G] [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (indGHtheta : ClassFunction G)
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi)
    (j : ι) :
    scalarProduct G indGHtheta (chi j) = e j := by
  rw [hdecomp]
  exact scalarProduct_weightedFamilySum_left_orthonormal
    (fun i => (e i : ℂ)) chi horth j

public theorem proposition_1_7_inertia_multiplicity_from_decomposition
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (j : ι) :
    scalarProduct T
        (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) (psi j) =
      e j :=
  proposition_1_7_multiplicity_from_decomposition e psi
    (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta))
    horthT hdecompT j

/-! ## Lying above and coefficient extraction -/

@[expose] public def LiesAbove
    {G : Type*} [Group G] (H T : Subgroup G) [Finite T]
    (psi : ClassFunction T) (theta : ClassFunction H) : Prop :=
  scalarProduct (H.subgroupOf T) (subgroupOfClassFunction theta)
    (subgroupRestriction (H.subgroupOf T) psi) ≠ 0

public theorem liesAbove_iff_scalarProduct_induced_ne_zero
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T]
    (psi : ClassFunction T) (theta : ClassFunction H)
    (hpsi : IsClassFunction psi) :
    LiesAbove H T psi theta ↔
      scalarProduct T
        (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) psi ≠ 0 := by
  rw [LiesAbove]
  rw [inducedClassFunction_frobenius_general (H.subgroupOf T)
    (subgroupOfClassFunction theta) psi hpsi]

public theorem proposition_1_7_liesAbove_iff_multiplicity_ne_zero
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hclass : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (i : ι) :
    LiesAbove H T (psi i) theta ↔ e i ≠ 0 := by
  rw [liesAbove_iff_scalarProduct_induced_ne_zero H T (psi i) theta (hclass i)]
  have hi := proposition_1_7_inertia_multiplicity_from_decomposition
    H T e psi theta horthT hdecompT i
  constructor
  · intro hnonzero hzero
    apply hnonzero
    rw [hi, hzero]
    norm_num
  · intro hnonzero
    rw [hi]
    exact_mod_cast hnonzero

public theorem proposition_1_7_liesAbove_of_positive_multiplicity
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hclass : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (i : ι) (hpos : 0 < e i) :
    LiesAbove H T (psi i) theta := by
  exact (proposition_1_7_liesAbove_iff_multiplicity_ne_zero H T e psi theta
    hclass horthT hdecompT i).2 (Nat.ne_of_gt hpos)

public theorem proposition_1_7_equal_multiplicities_of_equal_restrictions
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (i0 : ι)
    (hclass : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hres : ∀ i : ι,
      subgroupRestriction (H.subgroupOf T) (psi i) =
        subgroupRestriction (H.subgroupOf T) (psi i0)) :
    ∀ i : ι, e i = e i0 := by
  intro i
  have hi := proposition_1_7_inertia_multiplicity_from_decomposition
    H T e psi theta horthT hdecompT i
  have h0 := proposition_1_7_inertia_multiplicity_from_decomposition
    H T e psi theta horthT hdecompT i0
  have hC : (e i : ℂ) = (e i0 : ℂ) := by
    rw [← hi, ← h0]
    rw [inducedClassFunction_frobenius_general (H.subgroupOf T)
      (subgroupOfClassFunction theta) (psi i) (hclass i)]
    rw [inducedClassFunction_frobenius_general (H.subgroupOf T)
      (subgroupOfClassFunction theta) (psi i0) (hclass i0)]
    rw [hres i]
  exact_mod_cast hC

public theorem subgroupRestriction_mul_left_eq_of_one_on_subgroup
    {G : Type*} [Group G] (H T : Subgroup G)
    (lambda psi : ClassFunction T)
    (hlambda : ∀ h : H.subgroupOf T, lambda h = 1) :
    subgroupRestriction (H.subgroupOf T) (lambda * psi) =
      subgroupRestriction (H.subgroupOf T) psi := by
  ext h
  simp [subgroupRestriction, hlambda h]

public theorem proposition_1_7_equal_restrictions_of_twists
    {G ι : Type*} [Group G]
    (H T : Subgroup G) (lambda : ι → ClassFunction T)
    (psi : ι → ClassFunction T) (i0 : ι)
    (htwist : ∀ i : ι, psi i = lambda i * psi i0)
    (hlambda : ∀ i : ι, ∀ h : H.subgroupOf T, lambda i h = 1) :
    ∀ i : ι,
      subgroupRestriction (H.subgroupOf T) (psi i) =
        subgroupRestriction (H.subgroupOf T) (psi i0) := by
  intro i
  rw [htwist i]
  exact subgroupRestriction_mul_left_eq_of_one_on_subgroup H T
    (lambda i) (psi i0) (hlambda i)

public theorem proposition_1_7_equal_multiplicities_of_twists
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (lambda : ι → ClassFunction T)
    (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (i0 : ι)
    (hclass : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (htwist : ∀ i : ι, psi i = lambda i * psi i0)
    (hlambda : ∀ i : ι, ∀ h : H.subgroupOf T, lambda i h = 1) :
    ∀ i : ι, e i = e i0 :=
  proposition_1_7_equal_multiplicities_of_equal_restrictions H T e psi theta i0
    hclass horthT hdecompT
    (proposition_1_7_equal_restrictions_of_twists H T lambda psi i0 htwist hlambda)

/-! ## Linear characters of a finite abelian quotient -/

@[expose] public def quotientIsAbelian
    {G : Type*} [Group G] (H T : Subgroup G) : Prop :=
  ∀ x y : T, ((x * y * (y * x)⁻¹ : T) ∈ H.subgroupOf T)

public theorem finite_abelian_character_sum_apply
    {Q : Type*} [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)] (q : Q) :
    (∑ chi : Q →* ℂˣ, (chi q : ℂ)) =
      if q = 1 then (Nat.card Q : ℂ) else 0 := by
  classical
  by_cases hq : q = 1
  · have hcard :
        Fintype.card (Q →* ℂˣ) = Nat.card Q := by
      rw [← Nat.card_eq_fintype_card]
      exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
    rw [if_pos hq]
    calc
      (∑ chi : Q →* ℂˣ, (chi q : ℂ)) =
          (Fintype.card (Q →* ℂˣ) : ℂ) := by
            simp [hq]
      _ = (Nat.card Q : ℂ) := by
            exact_mod_cast hcard
  · rcases CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q ℂ hq with
      ⟨eta, heta⟩
    let S : ℂ := ∑ chi : Q →* ℂˣ, (chi q : ℂ)
    have hperm :
        S = ∑ chi : Q →* ℂˣ, ((eta * chi) q : ℂ) := by
      simpa [S] using
        (Equiv.sum_comp (Equiv.mulLeft eta)
          (fun chi : Q →* ℂˣ => (chi q : ℂ))).symm
    have hmul :
        (∑ chi : Q →* ℂˣ, ((eta * chi) q : ℂ)) =
          (eta q : ℂ) * S := by
      simp [S, Finset.mul_sum]
    have hfixed : S = (eta q : ℂ) * S := hperm.trans hmul
    have hzero : ((eta q : ℂ) - 1) * S = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr hfixed.symm
    have hetaC : (eta q : ℂ) - 1 ≠ 0 := by
      intro h
      apply heta
      ext
      exact sub_eq_zero.mp h
    have hSzero : S = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hetaC
    rw [if_neg hq]
    exact hSzero

@[expose] public noncomputable def quotientCharacterInflation
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) : ClassFunction T :=
  fun t => (chi (t : T ⧸ H.subgroupOf T) : ℂ)

public theorem quotientCharacterInflation_apply
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) (t : T) :
    quotientCharacterInflation H T chi t =
      (chi (t : T ⧸ H.subgroupOf T) : ℂ) := rfl

public theorem quotientCharacterInflation_one_on_subgroup
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    ∀ h : H.subgroupOf T, quotientCharacterInflation H T chi h = 1 := by
  intro h
  have hq : (h : T ⧸ H.subgroupOf T) = 1 :=
    (QuotientGroup.eq_one_iff (N := H.subgroupOf T) h).2 h.2
  simp [quotientCharacterInflation, hq]

public theorem quotientCharacterInflation_degree
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    degree (quotientCharacterInflation H T chi) = 1 := by
  simp [degree, quotientCharacterInflation]

@[expose] public noncomputable def characterInflationByHom
    {T Q : Type*} [Group T] [Group Q]
    (pi : T →* Q) (chi : Q →* ℂˣ) : ClassFunction T :=
  fun t => (chi (pi t) : ℂ)

public theorem characterInflationByHom_apply
    {T Q : Type*} [Group T] [Group Q]
    (pi : T →* Q) (chi : Q →* ℂˣ) (t : T) :
    characterInflationByHom pi chi t = (chi (pi t) : ℂ) := rfl

public theorem characterInflationByHom_one_on_kernel
    {T Q : Type*} [Group T] [Group Q]
    (S : Subgroup T) (pi : T →* Q)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ S)
    (chi : Q →* ℂˣ) :
    ∀ s : S, characterInflationByHom pi chi s = 1 := by
  intro s
  have hs : pi s = 1 := (hker s).2 s.2
  simp [characterInflationByHom, hs]

public theorem isClassFunction_mul
    {G : Type*} [Group G] (phi psi : ClassFunction G)
    (hphi : IsClassFunction phi) (hpsi : IsClassFunction psi) :
    IsClassFunction (phi * psi) := by
  intro x g
  simp [hphi x g, hpsi x g]

public theorem characterInflationByHom_isClassFunction
    {T Q : Type*} [Group T] [Group Q]
    (pi : T →* Q) (chi : Q →* ℂˣ) :
    IsClassFunction (characterInflationByHom pi chi) := by
  intro x t
  simp [characterInflationByHom, mul_assoc]

public theorem quotientCharacterInflation_isClassFunction
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    IsClassFunction (quotientCharacterInflation H T chi) := by
  simpa [quotientCharacterInflation, characterInflationByHom] using
    characterInflationByHom_isClassFunction
      (QuotientGroup.mk' (H.subgroupOf T)) chi

public theorem representationCharacter_mul_of_fin_one
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g h : G) :
    ρ.character (g * h) = ρ.character g * ρ.character h := by
  have hdim : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by simp
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
  obtain ⟨d, hd, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ h)
  have hρgh : ρ (g * h) = (c * d) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
    rw [map_mul, hc, hd]
    ext v i
    simp [mul_smul, mul_left_comm]
  have hρg : ρ.character g = c := by
    rw [Representation.character, hc]
    simp [hdim]
  have hρh : ρ.character h = d := by
    rw [Representation.character, hd]
    simp [hdim]
  rw [Representation.character, hρgh, hρg, hρh]
  simp [hdim]

public theorem representationCharacter_ne_zero_of_fin_one
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g : G) :
    ρ.character g ≠ 0 := by
  have hmul := representationCharacter_mul_of_fin_one ρ g g⁻¹
  have hone : ρ.character (g * g⁻¹) = 1 := by simp [Representation.character]
  intro hzero
  rw [hone, hzero] at hmul
  simp at hmul

public noncomputable def linearCharacterOfFinOneRepresentation
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) : G →* ℂˣ where
  toFun g := Units.mk0 (ρ.character g) (representationCharacter_ne_zero_of_fin_one ρ g)
  map_one' := by
    apply Units.ext
    simp [Representation.character]
  map_mul' g h := by
    apply Units.ext
    simp [representationCharacter_mul_of_fin_one ρ g h]

public theorem quotient_twist_isClassFunction
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ)
    (psi : ClassFunction T) (hpsi : IsClassFunction psi) :
    IsClassFunction (quotientCharacterInflation H T chi * psi) :=
  isClassFunction_mul (quotientCharacterInflation H T chi) psi
    (quotientCharacterInflation_isClassFunction H T chi) hpsi

public theorem subgroupRestriction_quotientCharacterInflation_mul
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ)
    (psi : ClassFunction T) :
    subgroupRestriction (H.subgroupOf T)
        (quotientCharacterInflation H T chi * psi) =
      subgroupRestriction (H.subgroupOf T) psi :=
  subgroupRestriction_mul_left_eq_of_one_on_subgroup H T
    (quotientCharacterInflation H T chi) psi
    (quotientCharacterInflation_one_on_subgroup H T chi)

public theorem quotient_twist_family_isClassFunction
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (psi : ((T ⧸ H.subgroupOf T) →* ℂˣ) → ClassFunction T)
    (chi0 : (T ⧸ H.subgroupOf T) →* ℂˣ)
    (hpsi0 : IsClassFunction (psi chi0))
    (htwist : ∀ chi : (T ⧸ H.subgroupOf T) →* ℂˣ,
      psi chi = quotientCharacterInflation H T chi * psi chi0) :
    ∀ chi : (T ⧸ H.subgroupOf T) →* ℂˣ, IsClassFunction (psi chi) := by
  intro chi
  rw [htwist chi]
  exact quotient_twist_isClassFunction H T chi (psi chi0) hpsi0

public theorem proposition_1_7_equal_restrictions_of_quotient_twists
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (psi : ((T ⧸ H.subgroupOf T) →* ℂˣ) → ClassFunction T)
    (chi0 : (T ⧸ H.subgroupOf T) →* ℂˣ)
    (htwist : ∀ chi : (T ⧸ H.subgroupOf T) →* ℂˣ,
      psi chi = quotientCharacterInflation H T chi * psi chi0) :
    ∀ chi : (T ⧸ H.subgroupOf T) →* ℂˣ,
      subgroupRestriction (H.subgroupOf T) (psi chi) =
        subgroupRestriction (H.subgroupOf T) (psi chi0) := by
  exact proposition_1_7_equal_restrictions_of_twists H T
    (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ => quotientCharacterInflation H T chi)
    psi chi0 htwist
    (fun chi => quotientCharacterInflation_one_on_subgroup H T chi)

public theorem characterInflationByHom_regular_sum
    {T Q : Type*} [Group T] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (S : Subgroup T) [DecidablePred (fun t : T => t ∈ S)]
    (pi : T →* Q)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ S)
    (hcard : Nat.card Q = Subgroup.index S)
    (t : T) :
    (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
      if t ∈ S then (Subgroup.index S : ℂ) else 0 := by
  classical
  have hsum := finite_abelian_character_sum_apply (Q := Q) (pi t)
  by_cases ht : t ∈ S
  · have hpi : pi t = 1 := (hker t).2 ht
    rw [if_pos ht]
    calc
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
          ∑ chi : Q →* ℂˣ, (chi (pi t) : ℂ) := rfl
      _ = (Nat.card Q : ℂ) := by
          rw [hsum, if_pos hpi]
      _ = (Subgroup.index S : ℂ) := by
          rw [hcard]
  · have hpi : pi t ≠ 1 := by
      intro h
      exact ht ((hker t).1 h)
    rw [if_neg ht]
    calc
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
          ∑ chi : Q →* ℂˣ, (chi (pi t) : ℂ) := rfl
      _ = 0 := by
          rw [hsum, if_neg hpi]

public theorem characterInflationByHom_regular_sum_mem
    {T Q : Type*} [Group T] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (S : Subgroup T) [DecidablePred (fun t : T => t ∈ S)]
    (pi : T →* Q)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ S)
    (hcard : Nat.card Q = Subgroup.index S) :
    ∀ t : T, t ∈ S →
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
        (Subgroup.index S : ℂ) := by
  intro t ht
  rw [characterInflationByHom_regular_sum S pi hker hcard t, if_pos ht]

public theorem characterInflationByHom_regular_sum_not_mem
    {T Q : Type*} [Group T] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (S : Subgroup T) [DecidablePred (fun t : T => t ∈ S)]
    (pi : T →* Q)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ S)
    (hcard : Nat.card Q = Subgroup.index S) :
    ∀ t : T, t ∉ S →
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) = 0 := by
  intro t ht
  rw [characterInflationByHom_regular_sum S pi hker hcard t, if_neg ht]

public theorem quotientCharacterInflation_regular_sum
    {G : Type*} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    (hquot_comm :
      Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y))
    [Finite ((T ⧸ H.subgroupOf T) →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (T ⧸ H.subgroupOf T))]
    [DecidablePred (fun t : T => t ∈ H.subgroupOf T)]
    (t : T) :
    (∑ chi : (T ⧸ H.subgroupOf T) →* ℂˣ,
        quotientCharacterInflation H T chi t) =
      if t ∈ H.subgroupOf T then (Subgroup.index (H.subgroupOf T) : ℂ) else 0 := by
  classical
  letI : CommGroup (T ⧸ H.subgroupOf T) :=
    { (inferInstance : Group (T ⧸ H.subgroupOf T)) with
      mul_comm := fun x y => hquot_comm.comm x y }
  have hker :
      ∀ t : T,
        (QuotientGroup.mk' (H.subgroupOf T)) t = 1 ↔ t ∈ H.subgroupOf T := by
    intro t
    change (t : T ⧸ H.subgroupOf T) = 1 ↔ t ∈ H.subgroupOf T
    exact QuotientGroup.eq_one_iff (N := H.subgroupOf T) t
  simpa [quotientCharacterInflation, characterInflationByHom] using
    (characterInflationByHom_regular_sum
      (T := T) (Q := T ⧸ H.subgroupOf T) (H.subgroupOf T)
      (QuotientGroup.mk' (H.subgroupOf T)) hker rfl t)

public theorem induced_restriction_eq_regular_twist_sum
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    [hHsub : (H.subgroupOf T).Normal]
    (psi : ClassFunction T) (lambda : ι → ClassFunction T)
    (hpsi : IsClassFunction psi)
    (hregular_mem : ∀ t : T, t ∈ H.subgroupOf T →
      (∑ i : ι, lambda i t) = (Subgroup.index (H.subgroupOf T) : ℂ))
    (hregular_not_mem : ∀ t : T, t ∉ H.subgroupOf T →
      (∑ i : ι, lambda i t) = 0) :
    inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) =
      familySum (fun i : ι => lambda i * psi) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let Hsub : Subgroup T := H.subgroupOf T
  letI : Fintype Hsub := Fintype.ofFinite Hsub
  have hcardH_ne : (Nat.card Hsub : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Hsub)).ne'
  have hindex_card : (Subgroup.index Hsub : ℂ) * Nat.card Hsub = Nat.card T := by
    exact_mod_cast Hsub.index_mul_card
  have hcoef : (Nat.card Hsub : ℂ)⁻¹ * (Nat.card T : ℂ) =
      (Subgroup.index Hsub : ℂ) := by
    have hindex_card' :
        (Nat.card T : ℂ) = (Subgroup.index Hsub : ℂ) * Nat.card Hsub := by
      simpa [mul_comm] using hindex_card.symm
    rw [hindex_card']
    field_simp [hcardH_ne]
  ext t
  by_cases htH : t ∈ Hsub
  · have hsum :
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ Hsub then
            subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
          else 0) =
        (Nat.card T : ℂ) * psi t := by
      calc
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ Hsub then
            subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
          else 0) = ∑ _x : T, psi t := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            have hxmem : x * t * x⁻¹ ∈ Hsub := hHsub.conj_mem t htH x
            have hclass : psi (x * t * x⁻¹) = psi t := hpsi x t
            simp [subgroupRestriction, hxmem, hclass]
        _ = (Nat.card T : ℂ) * psi t := by
            simp [Finset.card_univ]
    calc
      inducedCF Hsub (subgroupRestriction Hsub psi) t =
          (Nat.card Hsub : ℂ)⁻¹ *
            ∑ x : T,
              if hx : x * t * x⁻¹ ∈ Hsub then
                subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
              else 0 := by
            unfold inducedCF inducedClassFunction
            rfl
      _ = ((Nat.card Hsub : ℂ)⁻¹ * (Nat.card T : ℂ)) * psi t := by
            rw [hsum]
            ring
      _ = (Subgroup.index Hsub : ℂ) * psi t := by
            rw [hcoef]
      _ = (∑ i : ι, lambda i t) * psi t := by
            rw [hregular_mem t htH]
      _ = familySum (fun i : ι => lambda i * psi) t := by
            simp [familySum, Finset.sum_mul]
  · have hsum :
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ Hsub then
            subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _hx
      have hxnot : ¬ x * t * x⁻¹ ∈ Hsub := by
        intro hxmem
        apply htH
        have hback : x⁻¹ * (x * t * x⁻¹) * x ∈ Hsub := by
          simpa [Hsub] using hHsub.conj_mem (x * t * x⁻¹) hxmem x⁻¹
        simpa [mul_assoc] using hback
      simp [hxnot]
    calc
      inducedCF Hsub (subgroupRestriction Hsub psi) t =
          (Nat.card Hsub : ℂ)⁻¹ *
            ∑ x : T,
              if hx : x * t * x⁻¹ ∈ Hsub then
                subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
              else 0 := by
            unfold inducedCF inducedClassFunction
            rfl
      _ = 0 := by
            rw [hsum]
            simp
      _ = (∑ i : ι, lambda i t) * psi t := by
            rw [hregular_not_mem t htH]
            simp
      _ = familySum (fun i : ι => lambda i * psi) t := by
            simp [familySum, Finset.sum_mul]

public theorem induced_restriction_eq_regular_twist_sum_of_global_normal
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T] [H.Normal]
    (psi : ClassFunction T) (lambda : ι → ClassFunction T)
    (hpsi : IsClassFunction psi)
    (hregular_mem : ∀ t : T, t ∈ H.subgroupOf T →
      (∑ i : ι, lambda i t) = (Subgroup.index (H.subgroupOf T) : ℂ))
    (hregular_not_mem : ∀ t : T, t ∉ H.subgroupOf T →
      (∑ i : ι, lambda i t) = 0) :
    inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) =
      familySum (fun i : ι => lambda i * psi) := by
  letI : (H.subgroupOf T).Normal := subgroupOf_normal_of_normal H T
  exact induced_restriction_eq_regular_twist_sum H T psi lambda hpsi
    hregular_mem hregular_not_mem

public theorem induced_restriction_eq_regular_inflated_character_sum
    {G Q : Type*} [Group G] [Finite G] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (H T : Subgroup G) [Finite H] [Finite T]
    [(H.subgroupOf T).Normal]
    [DecidablePred (fun t : T => t ∈ H.subgroupOf T)]
    (psi : ClassFunction T) (pi : T →* Q)
    (hpsi : IsClassFunction psi)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ H.subgroupOf T)
    (hcard : Nat.card Q = Subgroup.index (H.subgroupOf T)) :
    inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) =
      familySum (fun chi : Q →* ℂˣ => characterInflationByHom pi chi * psi) := by
  exact induced_restriction_eq_regular_twist_sum H T psi
    (fun chi : Q →* ℂˣ => characterInflationByHom pi chi) hpsi
    (characterInflationByHom_regular_sum_mem (H.subgroupOf T) pi hker hcard)
    (characterInflationByHom_regular_sum_not_mem (H.subgroupOf T) pi hker hcard)

public theorem induced_restriction_eq_regular_quotient_twist_sum
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T]
    [(H.subgroupOf T).Normal]
    (hquot_comm :
      Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y))
    [Finite ((T ⧸ H.subgroupOf T) →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (T ⧸ H.subgroupOf T))]
    [DecidablePred (fun t : T => t ∈ H.subgroupOf T)]
    (psi : ClassFunction T) (hpsi : IsClassFunction psi) :
    inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) =
      familySum
        (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
          quotientCharacterInflation H T chi * psi) := by
  classical
  letI : CommGroup (T ⧸ H.subgroupOf T) :=
    { (inferInstance : Group (T ⧸ H.subgroupOf T)) with
      mul_comm := fun x y => hquot_comm.comm x y }
  have hker :
      ∀ t : T,
        (QuotientGroup.mk' (H.subgroupOf T)) t = 1 ↔ t ∈ H.subgroupOf T := by
    intro t
    change (t : T ⧸ H.subgroupOf T) = 1 ↔ t ∈ H.subgroupOf T
    exact QuotientGroup.eq_one_iff (N := H.subgroupOf T) t
  simpa [quotientCharacterInflation, characterInflationByHom] using
    (induced_restriction_eq_regular_inflated_character_sum
      (H := H) (T := T) (Q := T ⧸ H.subgroupOf T) psi
      (QuotientGroup.mk' (H.subgroupOf T)) hpsi hker rfl)

public theorem quotient_twist_sum_eq_smul_induced_of_restriction
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T]
    [(H.subgroupOf T).Normal]
    (hquot_comm :
      Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y))
    [Finite ((T ⧸ H.subgroupOf T) →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (T ⧸ H.subgroupOf T))]
    [DecidablePred (fun t : T => t ∈ H.subgroupOf T)]
    (psi : ClassFunction T) (theta : ClassFunction H) (e : ℕ)
    (hpsi : IsClassFunction psi)
    (hres :
      subgroupRestriction (H.subgroupOf T) psi =
        (e : ℂ) • subgroupOfClassFunction theta) :
    (e : ℂ) • inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
      familySum
        (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
          quotientCharacterInflation H T chi * psi) := by
  have hregular :=
    induced_restriction_eq_regular_quotient_twist_sum H T hquot_comm psi hpsi
  calc
    (e : ℂ) • inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        inducedCF (H.subgroupOf T) ((e : ℂ) • subgroupOfClassFunction theta) := by
          exact (inducedClassFunction_smul (H.subgroupOf T) (e : ℂ)
            (subgroupOfClassFunction theta)).symm
    _ = inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) := by
          rw [hres]
    _ = familySum
        (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
          quotientCharacterInflation H T chi * psi) := hregular

/-! ### Twisting irreducible characters by quotient-linear characters -/

public theorem complex_hasEnoughRootsOfUnity (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity ℂ n := by
  exact HasEnoughRootsOfUnity.of_card_le (R := ℂ) (n := n)
    (by simp [Complex.card_rootsOfUnity])

public theorem quotientIsAbelian_commutative
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (hquot : quotientIsAbelian H T) :
    Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y) := by
  refine ⟨?_⟩
  intro q r
  refine QuotientGroup.induction_on q ?_
  intro x
  refine QuotientGroup.induction_on r ?_
  intro y
  change ((x * y : T) : T ⧸ H.subgroupOf T) =
    ((y * x : T) : T ⧸ H.subgroupOf T)
  rw [QuotientGroup.eq]
  have hmem : x * y * (y * x)⁻¹ ∈ H.subgroupOf T := hquot x y
  have hinv : (x * y * (y * x)⁻¹)⁻¹ ∈ H.subgroupOf T :=
    (H.subgroupOf T).inv_mem hmem
  have hconj :
      ((x * y : T)⁻¹ * ((x * y * (y * x)⁻¹)⁻¹) * (x * y : T)) ∈
        H.subgroupOf T := by
    have hnormal : (H.subgroupOf T).Normal := inferInstance
    simpa using hnormal.conj_mem _ hinv (x * y)⁻¹
  simpa [mul_assoc] using hconj

public def representationTwistByCharacter
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V) :
    Representation ℂ G V where
  toFun g := (lambda g : ℂ) • rho g
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    change (lambda (x * y) : ℂ) • rho (x * y) v =
      (lambda x : ℂ) • rho x ((lambda y : ℂ) • rho y v)
    rw [map_mul lambda]
    rw [map_mul rho]
    simp only [Units.val_mul]
    change ((lambda x : ℂ) * (lambda y : ℂ)) • (rho x ((rho y) v)) =
      (lambda x : ℂ) • rho x ((lambda y : ℂ) • rho y v)
    rw [map_smul]
    rw [smul_smul]

public theorem representationTwistByCharacter_character
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V) :
    (representationTwistByCharacter lambda rho).character =
      (fun g : G => (lambda g : ℂ)) * rho.character := by
  funext g
  simp [representationTwistByCharacter, Representation.character]

def subrepresentationOrderIso_twistByCharacter
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V) :
    Subrepresentation rho ≃o
      Subrepresentation (representationTwistByCharacter lambda rho) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        exact S.toSubmodule.smul_mem (lambda g : ℂ)
          (S.apply_mem_toSubmodule g hv) }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        have htw := S.apply_mem_toSubmodule g hv
        dsimp [representationTwistByCharacter] at htw
        have hback :
            ((lambda g : ℂ)⁻¹) • ((lambda g : ℂ) • rho g v) ∈
              S.toSubmodule :=
          S.toSubmodule.smul_mem ((lambda g : ℂ)⁻¹) htw
        have hunit : (lambda g : ℂ) ≠ 0 := Units.ne_zero (lambda g)
        simpa [smul_smul, inv_mul_cancel₀ hunit] using hback }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro S T
    rfl

public theorem irreducible_twistByCharacter
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V)
    (hirr : Representation.IsIrreducible rho) :
    Representation.IsIrreducible (representationTwistByCharacter lambda rho) := by
  letI : Representation.IsIrreducible rho := hirr
  exact (OrderIso.isSimpleOrder_iff
    (subrepresentationOrderIso_twistByCharacter lambda rho)).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
public theorem characterInflationByHom_isIrreducibleCharacterOnGroup
    {T Q : Type u} [Group T] [Finite T] [Group Q]
    (π : T →* Q) (χ : Q →* ℂˣ) :
    IsIrreducibleCharacterOnGroup (characterInflationByHom π χ) := by
  let lambda : T →* ℂˣ := χ.comp π
  let ρ0 : Representation ℂ T (Fin 1 → ℂ) := Representation.trivial ℂ T (Fin 1 → ℂ)
  have hρ0irr : Representation.IsIrreducible ρ0 := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ T) (V := ρ0.asModule) (by
        change Module.finrank ℂ (Fin 1 → ℂ) = 1
        simp)
  let ρ : Representation ℂ T (Fin 1 → ℂ) :=
    representationTwistByCharacter lambda ρ0
  have hρirr : Representation.IsIrreducible ρ :=
    irreducible_twistByCharacter lambda ρ0 hρ0irr
  have hρ0char : ρ0.character = principalCharacter T := by
    ext t
    simp [ρ0, principalCharacter, Representation.character]
  have hchar :
      characterInflationByHom π χ = ρ.character := by
    calc
      characterInflationByHom π χ =
          (fun t : T => (lambda t : ℂ)) * principalCharacter T := by
            ext t
            simp [lambda, characterInflationByHom, principalCharacter]
      _ = (fun t : T => (lambda t : ℂ)) * ρ0.character := by rw [hρ0char]
      _ = ρ.character := by
            simpa [ρ] using
              (representationTwistByCharacter_character lambda ρ0).symm
  exact ⟨1, ρ, hρirr, hchar⟩

public theorem quotientCharacterInflation_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    (χ : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    IsIrreducibleCharacterOnGroup (quotientCharacterInflation H T χ) := by
  simpa [quotientCharacterInflation, characterInflationByHom] using
    characterInflationByHom_isIrreducibleCharacterOnGroup
      (QuotientGroup.mk' (H.subgroupOf T)) χ

public theorem quotientCharacterInflation_injective
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal] :
    Function.Injective
      (fun χ : (T ⧸ H.subgroupOf T) →* ℂˣ =>
        quotientCharacterInflation H T χ) := by
  intro χ η hEq
  ext q
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (H.subgroupOf T) q
  have hval := congrFun hEq t
  simpa [quotientCharacterInflation, ← ht] using hval

public theorem quotientCharacterInflation_ne_principal_of_ne_one
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal]
    {χ : (T ⧸ H.subgroupOf T) →* ℂˣ} (hχ : χ ≠ 1) :
    quotientCharacterInflation H T χ ≠ principalCharacter T := by
  intro hprin
  apply hχ
  have hone :
      quotientCharacterInflation H T (1 : (T ⧸ H.subgroupOf T) →* ℂˣ) =
        principalCharacter T := by
    ext t
    simp [quotientCharacterInflation, principalCharacter]
  exact quotientCharacterInflation_injective H T (hprin.trans hone.symm)

public theorem subgroupInKernel'_quotientCharacterInflation
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal]
    (χ : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    subgroupInKernel' (quotientCharacterInflation H T χ) (H.subgroupOf T) := by
  intro h
  rw [quotientCharacterInflation_one_on_subgroup H T χ h]
  rw [quotientCharacterInflation_degree]

public theorem linearCharacter_isClassFunction
    {G : Type u} [Group G] (χ : G →* ℂˣ) :
    IsClassFunction (fun g : G => (χ g : ℂ)) := by
  intro x g
  simp [mul_assoc]

public theorem linearCharacter_degree
    {G : Type u} [Group G] (χ : G →* ℂˣ) :
    degree (fun g : G => (χ g : ℂ)) = 1 := by
  simp [degree]

public theorem exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
    {G : Type u} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    {θ : ClassFunction T}
    (hθirr : IsIrreducibleCharacterOnGroup θ)
    (hθker : subgroupInKernel' θ (H.subgroupOf T))
    (hθdeg : degree θ = 1) :
    ∃ χ : (T ⧸ H.subgroupOf T) →* ℂˣ,
      θ = quotientCharacterInflation H T χ := by
  classical
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hnC : (n : ℂ) = 1 := by
    simpa [hθeq, degree_representation_character ρ] using hθdeg
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let lam : T →* ℂˣ := linearCharacterOfFinOneRepresentation ρ
  have hHker : H.subgroupOf T ≤ lam.ker := by
    intro h hh
    change lam h = 1
    apply Units.ext
    change ρ.character h = 1
    have hval : θ h = 1 := by
      rw [hθker ⟨h, hh⟩]
      exact hθdeg
    simpa [hθeq] using hval
  let χ : (T ⧸ H.subgroupOf T) →* ℂˣ :=
    QuotientGroup.lift (H.subgroupOf T) lam hHker
  refine ⟨χ, ?_⟩
  ext t
  change θ t = (χ (t : T ⧸ H.subgroupOf T) : ℂ)
  rw [hθeq]
  simp [χ, lam, linearCharacterOfFinOneRepresentation]

public theorem exists_linearCharacter_of_irreducible_degree_one
    {G : Type u} [Group G] [Finite G]
    {θ : ClassFunction G}
    (hθirr : IsIrreducibleCharacterOnGroup θ)
    (hθdeg : degree θ = 1) :
    ∃ χ : G →* ℂˣ, θ = fun g : G => (χ g : ℂ) := by
  classical
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hnC : (n : ℂ) = 1 := by
    simpa [hθeq, degree_representation_character ρ] using hθdeg
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let lam : G →* ℂˣ := linearCharacterOfFinOneRepresentation ρ
  refine ⟨lam, ?_⟩
  ext g
  rw [hθeq]
  simp [lam, linearCharacterOfFinOneRepresentation]

public theorem isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ) :
    degree χ = 1 := by
  rcases hχ with ⟨n, ρ, hρirr, hχeq⟩
  have hfin : Module.finrank ℂ (Fin n → ℂ) = 1 := by
    letI : Representation.IsIrreducible ρ := hρirr
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
  rw [hχeq, degree_representation_character ρ]
  exact_mod_cast hfin

set_option backward.isDefEq.respectTransparency false in
public theorem scalarProduct_irreducibleCharacter_self
    {G : Type u} [Group G] [Finite G]
    {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ) :
    scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨_n, ρ, hρ, hχeq⟩
  rw [hχeq]
  exact scalarProduct_representation_char_self ρ hρ

set_option backward.isDefEq.respectTransparency false in
public theorem scalarProduct_irreducibleCharacter_eq_zero_of_ne
    {G : Type u} [Group G] [Finite G]
    {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ)
    (hψ : IsIrreducibleCharacterOnGroup ψ)
    (hne : χ ≠ ψ) :
    scalarProduct G χ ψ = 0 := by
  rcases hχ with ⟨_n, ρ, hρ, hχeq⟩
  rcases hψ with ⟨_m, σ, hσ, hψeq⟩
  exact scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      χ ψ ρ σ hχeq hψeq hρ hσ hne

/-- Every irreducible character of a direct product is the external product
of irreducible characters of its two factors. -/
public theorem exists_externalProductClassFunction_of_isIrreducibleCharacterOnGroup
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {theta : ClassFunction (G × H)}
    (htheta : IsIrreducibleCharacterOnGroup theta) :
    ∃ phi : ClassFunction G, ∃ psi : ClassFunction H,
      IsIrreducibleCharacterOnGroup phi ∧
        IsIrreducibleCharacterOnGroup psi ∧
        theta = externalProductClassFunction phi psi := by
  classical
  rcases Representation.card_irreducible_characters_eq_card_conjClasses
      (G := G) with ⟨iota, hiota, chi, hchi, hcardChi⟩
  rcases Representation.card_irreducible_characters_eq_card_conjClasses
      (G := H) with ⟨kappa, hkappa, psi, hpsi, hcardPsi⟩
  rcases Representation.card_irreducible_characters_eq_card_conjClasses
      (G := G × H) with ⟨lambda, hlambda, eta, heta, hcardEta⟩
  letI : Fintype iota := hiota
  letI : Fintype kappa := hkappa
  letI : Fintype lambda := hlambda
  let phi : iota → ClassFunction G := fun i => ofConjClassFunction (chi i)
  let psi' : kappa → ClassFunction H := fun j => ofConjClassFunction (psi j)
  have hphiIrr : ∀ i, IsIrreducibleCharacterOnGroup (phi i) := by
    intro i
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (phi i) (isBookIrreducibleCharacter_of_representation_irreducible
        (chi i) (hchi.1 i))
  have hpsiIrr : ∀ j, IsIrreducibleCharacterOnGroup (psi' j) := by
    intro j
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (psi' j) (isBookIrreducibleCharacter_of_representation_irreducible
        (psi j) (hpsi.1 j))
  let xi : iota × kappa → ClassFunction (G × H) := fun p =>
    externalProductClassFunction (phi p.1) (psi' p.2)
  have hxiIrr : ∀ p, IsIrreducibleCharacterOnGroup (xi p) := by
    intro p
    exact externalProductClassFunction_isIrreducibleCharacterOnGroup
      (hphiIrr p.1) (hpsiIrr p.2)
  have hxiClass : ∀ p, IsClassFunction (xi p) := by
    intro p
    exact externalProductClassFunction_isClassFunction
      (ofConjClassFunction_isClassFunction (chi p.1))
      (ofConjClassFunction_isClassFunction (psi p.2))
  have hxiInj : Function.Injective xi := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hcross :
        scalarProduct (G × H) (xi (i, j)) (xi (i', j')) =
          (if i = i' then 1 else 0) * (if j = j' then 1 else 0) := by
      rw [show xi (i, j) = externalProductClassFunction
          (ofConjClassFunction (chi i)) (ofConjClassFunction (psi j)) from rfl]
      rw [show xi (i', j') = externalProductClassFunction
          (ofConjClassFunction (chi i')) (ofConjClassFunction (psi j')) from rfl]
      rw [scalarProduct_externalProductClassFunction,
        scalarProduct_ofConjClassFunction,
        scalarProduct_ofConjClassFunction,
        representation_completeFamily_orthonormal hchi,
        representation_completeFamily_orthonormal hpsi]
    have hself :
        scalarProduct (G × H) (xi (i', j')) (xi (i', j')) = 1 :=
      scalarProduct_irreducibleCharacter_self (hxiIrr (i', j'))
    have hone :
        (if i = i' then (1 : ℂ) else 0) *
            (if j = j' then 1 else 0) = 1 := by
      calc
        _ = scalarProduct (G × H) (xi (i, j)) (xi (i', j')) := hcross.symm
        _ = scalarProduct (G × H) (xi (i', j')) (xi (i', j')) := by
          rw [hij]
        _ = 1 := hself
    have hi : i = i' := by
      by_contra hne
      simp [hne] at hone
    have hj : j = j' := by
      by_contra hne
      simp [hne] at hone
    exact Prod.ext hi hj
  let xibar : iota × kappa → Representation.ClassFunction (G × H) :=
    fun p => toConjClassFunction (xi p) (hxiClass p)
  have hxiBarIrr :
      ∀ p, Representation.IsIrreducibleCharacter (xibar p) := by
    intro p
    exact toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (hxiClass p) (hxiIrr p)
  let f : iota × kappa → lambda := fun p =>
    Classical.choose (heta.2.1 (xibar p) (hxiBarIrr p))
  have hf : ∀ p, eta (f p) = xibar p := by
    intro p
    exact Classical.choose_spec (heta.2.1 (xibar p) (hxiBarIrr p))
  have hfInj : Function.Injective f := by
    intro p q hpq
    apply hxiInj
    have hbar : xibar p = xibar q := by
      rw [← hf p, ← hf q, hpq]
    ext x
    have hx := congrFun hbar (ConjClasses.mk x)
    simpa [xibar, toConjClassFunction_apply] using hx
  have hcard : Fintype.card (iota × kappa) = Fintype.card lambda := by
    calc
      Fintype.card (iota × kappa) =
          Fintype.card iota * Fintype.card kappa := Fintype.card_prod iota kappa
      _ = Nat.card (ConjClasses G) * Nat.card (ConjClasses H) := by
        rw [hcardChi, hcardPsi]
      _ = Nat.card (ConjClasses (G × H)) := card_conjClasses_prod.symm
      _ = Fintype.card lambda := hcardEta.symm
  have hfSurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfInj, hcard⟩).2
  have hthetaClass : IsClassFunction theta :=
    isBookIrreducibleCharacter_isClassFunction theta
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup htheta)
  let thetabar : Representation.ClassFunction (G × H) :=
    toConjClassFunction theta hthetaClass
  have hthetaBarIrr : Representation.IsIrreducibleCharacter thetabar :=
    toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      hthetaClass htheta
  rcases heta.2.1 thetabar hthetaBarIrr with ⟨k, hk⟩
  rcases hfSurj k with ⟨p, hp⟩
  have hbar : xibar p = thetabar := by
    calc
      xibar p = eta (f p) := (hf p).symm
      _ = eta k := congrArg eta hp
      _ = thetabar := hk
  have hxiTheta : xi p = theta := by
    ext x
    have hx := congrFun hbar (ConjClasses.mk x)
    simpa [xibar, thetabar, toConjClassFunction_apply] using hx
  exact ⟨phi p.1, psi' p.2, hphiIrr p.1, hpsiIrr p.2, hxiTheta.symm⟩

public theorem isIrreducibleCharacterOnGroup_prod_iff
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {theta : ClassFunction (G × H)} :
    IsIrreducibleCharacterOnGroup theta ↔
      ∃ phi : ClassFunction G, ∃ psi : ClassFunction H,
        IsIrreducibleCharacterOnGroup phi ∧
          IsIrreducibleCharacterOnGroup psi ∧
          theta = externalProductClassFunction phi psi := by
  constructor
  · exact exists_externalProductClassFunction_of_isIrreducibleCharacterOnGroup
  · rintro ⟨phi, psi, hphi, hpsi, rfl⟩
    exact externalProductClassFunction_isIrreducibleCharacterOnGroup hphi hpsi

public theorem exists_externalProductClassFunction_of_isIrreducibleCharacterOnGroup_mulEquiv
    {G H K : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Group K] [Finite K] (e : G × H ≃* K)
    {theta : ClassFunction K}
    (htheta : IsIrreducibleCharacterOnGroup theta) :
    ∃ phi : ClassFunction G, ∃ psi : ClassFunction H,
      IsIrreducibleCharacterOnGroup phi ∧
        IsIrreducibleCharacterOnGroup psi ∧
        theta = classFunctionLinearEquivOfMulEquiv e
          (externalProductClassFunction phi psi) := by
  let theta' := (classFunctionLinearEquivOfMulEquiv e).symm theta
  have htheta' : IsIrreducibleCharacterOnGroup theta' := by
    simpa [theta', classFunctionLinearEquivOfMulEquiv_symm_eq] using
      (isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        e.symm htheta)
  rcases exists_externalProductClassFunction_of_isIrreducibleCharacterOnGroup
      htheta' with ⟨phi, psi, hphi, hpsi, hfactor⟩
  refine ⟨phi, psi, hphi, hpsi, ?_⟩
  calc
    theta = classFunctionLinearEquivOfMulEquiv e theta' :=
      ((classFunctionLinearEquivOfMulEquiv e).apply_symm_apply theta).symm
    _ = classFunctionLinearEquivOfMulEquiv e
        (externalProductClassFunction phi psi) := congrArg _ hfactor

/-- Transport conjugacy-class functions across a multiplicative
equivalence. -/
@[expose] public noncomputable def conjClassFunctionLinearEquivOfMulEquiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Representation.ClassFunction A ≃ₗ[ℂ] Representation.ClassFunction B where
  toFun phi :=
    toConjClassFunction
      (classFunctionLinearEquivOfMulEquiv e (ofConjClassFunction phi))
      (isClassFunction_classFunctionLinearEquivOfMulEquiv e
        (ofConjClassFunction_isClassFunction phi))
  invFun psi :=
    toConjClassFunction
      (classFunctionLinearEquivOfMulEquiv e.symm (ofConjClassFunction psi))
      (isClassFunction_classFunctionLinearEquivOfMulEquiv e.symm
        (ofConjClassFunction_isClassFunction psi))
  left_inv phi := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨a, rfl⟩
    change phi (ConjClasses.mk (e.symm (e a))) = phi (ConjClasses.mk a)
    rw [e.symm_apply_apply]
  right_inv psi := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨b, rfl⟩
    change psi (ConjClasses.mk (e (e.symm b))) = psi (ConjClasses.mk b)
    rw [e.apply_symm_apply]
  map_add' phi psi := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨b, rfl⟩
    rfl
  map_smul' z phi := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨b, rfl⟩
    rfl

public theorem conjClassFunctionLinearEquivOfMulEquiv_apply_mk
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (phi : Representation.ClassFunction A) (b : B) :
    conjClassFunctionLinearEquivOfMulEquiv e phi (ConjClasses.mk b) =
      phi (ConjClasses.mk (e.symm b)) := rfl

public theorem isIrreducibleCharacter_conjClassFunctionLinearEquivOfMulEquiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) {phi : Representation.ClassFunction A}
    (hphi : Representation.IsIrreducibleCharacter phi) :
    Representation.IsIrreducibleCharacter
      (conjClassFunctionLinearEquivOfMulEquiv e phi) := by
  exact toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    (isClassFunction_classFunctionLinearEquivOfMulEquiv e
      (ofConjClassFunction_isClassFunction phi))
    (isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv e
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        _ (isBookIrreducibleCharacter_of_representation_irreducible phi hphi)))

public theorem isCompleteIrreducibleCharacterFamily_conjClassFunctionLinearEquivOfMulEquiv
    {A B iota : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [Fintype iota] (e : A ≃* B)
    (chi : iota → Representation.ClassFunction A)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi) :
    Representation.IsCompleteIrreducibleCharacterFamily
      (fun i => conjClassFunctionLinearEquivOfMulEquiv e (chi i)) := by
  let E := conjClassFunctionLinearEquivOfMulEquiv e
  refine ⟨fun i =>
    isIrreducibleCharacter_conjClassFunctionLinearEquivOfMulEquiv e (hchi.1 i), ?_, ?_⟩
  · intro theta htheta
    have hpre : Representation.IsIrreducibleCharacter (E.symm theta) := by
      change Representation.IsIrreducibleCharacter
        (conjClassFunctionLinearEquivOfMulEquiv e.symm theta)
      exact isIrreducibleCharacter_conjClassFunctionLinearEquivOfMulEquiv
        e.symm htheta
    rcases hchi.2.1 (E.symm theta) hpre with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    calc
      E (chi i) = E (E.symm theta) := congrArg E hi
      _ = theta := E.apply_symm_apply theta
  · intro i j hij
    apply hchi.2.2
    exact E.injective hij

/-- External product in the conjugacy-class model of class functions. -/
@[expose] public noncomputable def externalProductConjClassFunction
    {G H : Type*} [Group G] [Group H]
    (phi : Representation.ClassFunction G)
    (psi : Representation.ClassFunction H) :
    Representation.ClassFunction (G × H) :=
  toConjClassFunction
    (externalProductClassFunction
      (ofConjClassFunction phi) (ofConjClassFunction psi))
    (externalProductClassFunction_isClassFunction
      (ofConjClassFunction_isClassFunction phi)
      (ofConjClassFunction_isClassFunction psi))

public theorem externalProductConjClassFunction_isIrreducibleCharacter
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {phi : Representation.ClassFunction G}
    {psi : Representation.ClassFunction H}
    (hphi : Representation.IsIrreducibleCharacter phi)
    (hpsi : Representation.IsIrreducibleCharacter psi) :
    Representation.IsIrreducibleCharacter
      (externalProductConjClassFunction phi psi) := by
  exact toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    (externalProductClassFunction_isClassFunction
      (ofConjClassFunction_isClassFunction phi)
      (ofConjClassFunction_isClassFunction psi))
    (externalProductClassFunction_isIrreducibleCharacterOnGroup
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        _ (isBookIrreducibleCharacter_of_representation_irreducible
          phi hphi))
      (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        _ (isBookIrreducibleCharacter_of_representation_irreducible
          psi hpsi)))

/-- An irreducible conjugacy-class function transported from a direct product
factors as the external product of irreducible component characters. -/
public theorem exists_externalProductConjClassFunction_of_isIrreducibleCharacter_mulEquiv
    {G H K : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Group K] [Finite K] (e : G × H ≃* K)
    {theta : Representation.ClassFunction K}
    (htheta : Representation.IsIrreducibleCharacter theta) :
    ∃ phi : Representation.ClassFunction G,
      ∃ psi : Representation.ClassFunction H,
        Representation.IsIrreducibleCharacter phi ∧
          Representation.IsIrreducibleCharacter psi ∧
          theta = conjClassFunctionLinearEquivOfMulEquiv e
            (externalProductConjClassFunction phi psi) := by
  let theta' : ClassFunction K := ofConjClassFunction theta
  have htheta'Irr : IsIrreducibleCharacterOnGroup theta' :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      theta' (isBookIrreducibleCharacter_of_representation_irreducible
        theta htheta)
  rcases exists_externalProductClassFunction_of_isIrreducibleCharacterOnGroup_mulEquiv
      e htheta'Irr with ⟨phi, psi, hphi, hpsi, hfactor⟩
  have hphiClass : IsClassFunction phi :=
    isBookIrreducibleCharacter_isClassFunction phi
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hphi)
  have hpsiClass : IsClassFunction psi :=
    isBookIrreducibleCharacter_isClassFunction psi
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hpsi)
  let phibar : Representation.ClassFunction G :=
    toConjClassFunction phi hphiClass
  let psibar : Representation.ClassFunction H :=
    toConjClassFunction psi hpsiClass
  have hphibar : Representation.IsIrreducibleCharacter phibar :=
    toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      hphiClass hphi
  have hpsibar : Representation.IsIrreducibleCharacter psibar :=
    toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      hpsiClass hpsi
  refine ⟨phibar, psibar, hphibar, hpsibar, ?_⟩
  ext c
  rcases ConjClasses.exists_rep c with ⟨k, rfl⟩
  have hk := congrFun hfactor k
  simpa [theta', phibar, psibar,
    conjClassFunctionLinearEquivOfMulEquiv_apply_mk,
    externalProductConjClassFunction, externalProductClassFunction,
    toConjClassFunction_apply, ofConjClassFunction] using hk

public theorem classFunctionInner_externalProductConjClassFunction
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (phi phi' : Representation.ClassFunction G)
    (psi psi' : Representation.ClassFunction H) :
    Representation.classFunctionInner
        (externalProductConjClassFunction phi psi)
        (externalProductConjClassFunction phi' psi') =
      Representation.classFunctionInner phi phi' *
        Representation.classFunctionInner psi psi' := by
  rw [show externalProductConjClassFunction phi psi =
      toConjClassFunction
        (externalProductClassFunction
          (ofConjClassFunction phi) (ofConjClassFunction psi))
        (externalProductClassFunction_isClassFunction
          (ofConjClassFunction_isClassFunction phi)
          (ofConjClassFunction_isClassFunction psi)) from rfl]
  rw [show externalProductConjClassFunction phi' psi' =
      toConjClassFunction
        (externalProductClassFunction
          (ofConjClassFunction phi') (ofConjClassFunction psi'))
        (externalProductClassFunction_isClassFunction
          (ofConjClassFunction_isClassFunction phi')
          (ofConjClassFunction_isClassFunction psi')) from rfl]
  rw [classFunctionInner_toConjClassFunction,
    scalarProduct_externalProductClassFunction,
    scalarProduct_ofConjClassFunction,
    scalarProduct_ofConjClassFunction]

/-- External products of two complete irreducible-character families form a
complete irreducible-character family of the direct product. -/
public theorem externalProductConjClassFunction_isCompleteIrreducibleCharacterFamily
    {G H iota kappa : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    [Fintype iota] [Fintype kappa]
    (chi : iota → Representation.ClassFunction G)
    (psi : kappa → Representation.ClassFunction H)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (hpsi : Representation.IsCompleteIrreducibleCharacterFamily psi) :
    Representation.IsCompleteIrreducibleCharacterFamily
      (fun p : iota × kappa =>
        externalProductConjClassFunction (chi p.1) (psi p.2)) := by
  classical
  let xi : iota × kappa → Representation.ClassFunction (G × H) :=
    fun p => externalProductConjClassFunction (chi p.1) (psi p.2)
  have hxiIrr : ∀ p, Representation.IsIrreducibleCharacter (xi p) := by
    intro p
    exact toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (externalProductClassFunction_isClassFunction
        (ofConjClassFunction_isClassFunction (chi p.1))
        (ofConjClassFunction_isClassFunction (psi p.2)))
      (externalProductClassFunction_isIrreducibleCharacterOnGroup
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          _ (isBookIrreducibleCharacter_of_representation_irreducible
            (chi p.1) (hchi.1 p.1)))
        (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          _ (isBookIrreducibleCharacter_of_representation_irreducible
            (psi p.2) (hpsi.1 p.2))))
  refine ⟨hxiIrr, ?_, ?_⟩
  · intro theta htheta
    let theta' : ClassFunction (G × H) := ofConjClassFunction theta
    have htheta'Irr : IsIrreducibleCharacterOnGroup theta' :=
      isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        theta' (isBookIrreducibleCharacter_of_representation_irreducible
          theta htheta)
    rcases exists_externalProductClassFunction_of_isIrreducibleCharacterOnGroup
        htheta'Irr with ⟨phi, tau, hphi, htau, hfactor⟩
    have hphiClass : IsClassFunction phi :=
      isBookIrreducibleCharacter_isClassFunction phi
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hphi)
    have htauClass : IsClassFunction tau :=
      isBookIrreducibleCharacter_isClassFunction tau
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup htau)
    let phibar : Representation.ClassFunction G :=
      toConjClassFunction phi hphiClass
    let taubar : Representation.ClassFunction H :=
      toConjClassFunction tau htauClass
    have hphibarIrr : Representation.IsIrreducibleCharacter phibar :=
      toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        hphiClass hphi
    have htaubarIrr : Representation.IsIrreducibleCharacter taubar :=
      toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        htauClass htau
    rcases hchi.2.1 phibar hphibarIrr with ⟨i, hi⟩
    rcases hpsi.2.1 taubar htaubarIrr with ⟨j, hj⟩
    refine ⟨(i, j), ?_⟩
    ext c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    rcases x with ⟨g, h⟩
    have hvalue := congrFun hfactor (g, h)
    change ofConjClassFunction (chi i) g *
        ofConjClassFunction (psi j) h = theta (ConjClasses.mk (g, h))
    rw [hi, hj]
    simpa [phibar, taubar, theta'] using hvalue.symm
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    change xi (i, j) = xi (i', j') at hij
    have hcross :
        Representation.classFunctionInner (xi (i, j)) (xi (i', j')) =
          (if i = i' then 1 else 0) * (if j = j' then 1 else 0) := by
      rw [show xi (i, j) =
          externalProductConjClassFunction (chi i) (psi j) from rfl]
      rw [show xi (i', j') =
          externalProductConjClassFunction (chi i') (psi j') from rfl]
      rw [classFunctionInner_externalProductConjClassFunction,
        representation_completeFamily_orthonormal hchi,
        representation_completeFamily_orthonormal hpsi]
    have hself :
        Representation.classFunctionInner (xi (i', j')) (xi (i', j')) = 1 :=
      (hxiIrr (i', j')).2
    have hone :
        (if i = i' then (1 : ℂ) else 0) *
            (if j = j' then 1 else 0) = 1 := by
      calc
        _ = Representation.classFunctionInner (xi (i, j)) (xi (i', j')) :=
          hcross.symm
        _ = Representation.classFunctionInner (xi (i', j')) (xi (i', j')) := by
          rw [hij]
        _ = 1 := hself
    have hi : i = i' := by
      by_contra hne
      simp [hne] at hone
    have hj : j = j' := by
      by_contra hne
      simp [hne] at hone
    exact Prod.ext hi hj

/-- In any complete family of irreducible characters, the degree-one members
are in bijection with the linear characters of the abelianization. -/
public theorem completeIrreducibleCharacterFamily_degree_one_card
    {G : Type u} {ι : Type v} [Group G] [Finite G]
    [Fintype ι] [DecidableEq ι]
    (chi : ι → Representation.ClassFunction G)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi) :
    (Finset.univ.filter fun i =>
      chi i (ConjClasses.mk (1 : G)) = 1).card =
      Nat.card (G ⧸ commutator G) := by
  classical
  let LinIdx := {i : ι // chi i (ConjClasses.mk (1 : G)) = 1}
  let Q := G ⧸ commutator G
  let QChar := Q →* ℂˣ
  let theta : LinIdx → ClassFunction G := fun i =>
    ofConjClassFunction (chi i.1)
  have hthetaIrr : ∀ i : LinIdx,
      IsIrreducibleCharacterOnGroup (theta i) := by
    intro i
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (theta i)
      (isBookIrreducibleCharacter_of_representation_irreducible
        (chi i.1) (hchi.1 i.1))
  have hthetaDegree : ∀ i : LinIdx, degree (theta i) = 1 := by
    intro i
    simpa [theta, degree, ofConjClassFunction] using i.2
  let linChar : LinIdx → G →* ℂˣ := fun i =>
    Classical.choose
      (exists_linearCharacter_of_irreducible_degree_one
        (hthetaIrr i) (hthetaDegree i))
  have hlinCharSpec : ∀ i : LinIdx,
      theta i = fun g : G => (linChar i g : ℂ) := by
    intro i
    exact Classical.choose_spec
      (exists_linearCharacter_of_irreducible_degree_one
        (hthetaIrr i) (hthetaDegree i))
  let toQ : LinIdx → QChar := fun i =>
    QuotientGroup.lift (commutator G) (linChar i)
      (Abelianization.commutator_subset_ker (linChar i))
  let inflated : QChar → ClassFunction G := fun psi =>
    characterInflationByHom (QuotientGroup.mk' (commutator G)) psi
  have hinflatedIrr : ∀ psi : QChar,
      IsIrreducibleCharacterOnGroup (inflated psi) := by
    intro psi
    exact characterInflationByHom_isIrreducibleCharacterOnGroup
      (QuotientGroup.mk' (commutator G)) psi
  have hinflatedClass : ∀ psi : QChar,
      IsClassFunction (inflated psi) := by
    intro psi
    exact characterInflationByHom_isClassFunction
      (QuotientGroup.mk' (commutator G)) psi
  let inflatedBar : QChar → Representation.ClassFunction G := fun psi =>
    toConjClassFunction (inflated psi) (hinflatedClass psi)
  have hinflatedBarIrr : ∀ psi : QChar,
      Representation.IsIrreducibleCharacter (inflatedBar psi) := by
    intro psi
    exact toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (hinflatedClass psi) (hinflatedIrr psi)
  let ofQIndex : QChar → ι := fun psi =>
    Classical.choose (hchi.2.1 (inflatedBar psi) (hinflatedBarIrr psi))
  have hofQIndexSpec : ∀ psi : QChar,
      chi (ofQIndex psi) = inflatedBar psi := by
    intro psi
    exact Classical.choose_spec
      (hchi.2.1 (inflatedBar psi) (hinflatedBarIrr psi))
  have hofQIndexDegree : ∀ psi : QChar,
      chi (ofQIndex psi) (ConjClasses.mk (1 : G)) = 1 := by
    intro psi
    rw [hofQIndexSpec]
    simp [inflatedBar, inflated, toConjClassFunction_apply,
      characterInflationByHom]
  let ofQ : QChar → LinIdx := fun psi =>
    ⟨ofQIndex psi, hofQIndexDegree psi⟩
  have htoQOfQ : ∀ psi : QChar, toQ (ofQ psi) = psi := by
    intro psi
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    apply Units.ext
    have hEq :
        (fun x : G => (linChar (ofQ psi) x : ℂ)) = inflated psi := by
      rw [← hlinCharSpec]
      dsimp [theta, ofQ]
      rw [hofQIndexSpec]
      ext x
      rfl
    have hg := congrFun hEq g
    simpa [toQ, inflated, characterInflationByHom] using hg
  have htoQInj : Function.Injective toQ := by
    intro i j hij
    have hval : i.1 = j.1 := by
      apply hchi.2.2
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      have hq := DFunLike.congr_fun hij
        (QuotientGroup.mk' (commutator G) g)
      have hqCoe := congrArg (fun z : ℂˣ => (z : ℂ)) hq
      have hi := congrFun (hlinCharSpec i) g
      have hj := congrFun (hlinCharSpec j) g
      simpa [theta, ofConjClassFunction, toQ] using
        hi.trans (hqCoe.trans hj.symm)
    exact Subtype.ext hval
  have htoQBij : Function.Bijective toQ := by
    refine ⟨htoQInj, ?_⟩
    intro psi
    exact ⟨ofQ psi, htoQOfQ psi⟩
  have hlinCard : Nat.card LinIdx = Nat.card QChar :=
    Nat.card_congr (Equiv.ofBijective toQ htoQBij)
  have hfilter :
      (Finset.univ.filter fun i =>
        chi i (ConjClasses.mk (1 : G)) = 1).card = Nat.card LinIdx := by
    rw [Nat.card_eq_fintype_card]
    simpa [LinIdx] using
      (Fintype.card_subtype
        (fun i => chi i (ConjClasses.mk (1 : G)) = 1)).symm
  have hQcard : Nat.card QChar = Nat.card Q := by
    letI : IsMulCommutative Q :=
      ⟨Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl⟩
    letI : CommGroup Q := CommGroup.ofIsMulCommutative
    letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
      complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
  rw [hfilter, hlinCard, hQcard]

public theorem isBookIrreducibleCharacter_twistByCharacter
    {G : Type u} [Group G] [Finite G]
    (lambda : G →* ℂˣ) (psi : ClassFunction G)
    (hpsi : IsBookIrreducibleCharacter psi) :
    IsBookIrreducibleCharacter ((fun g : G => (lambda g : ℂ)) * psi) := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      psi hpsi with
    ⟨V, _hadd, _hmod, _hfd, rho, hpsi_eq, hirr⟩
  let rhoTwist := representationTwistByCharacter lambda rho
  have hchar :
      ((fun g : G => (lambda g : ℂ)) * psi) = rhoTwist.character := by
    rw [hpsi_eq]
    exact (representationTwistByCharacter_character lambda rho).symm
  constructor
  · refine ⟨V, inferInstance, inferInstance, inferInstance, rhoTwist, ?_⟩
    exact hchar
  · rw [hchar]
    exact scalarProduct_representation_char_self rhoTwist
      (irreducible_twistByCharacter lambda rho hirr)

public theorem quotient_twist_isBookIrreducibleCharacter
    {G : Type u} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ)
    (psi : ClassFunction T)
    (hpsi : IsBookIrreducibleCharacter psi) :
    IsBookIrreducibleCharacter (quotientCharacterInflation H T chi * psi) := by
  let lambda : T →* ℂˣ := chi.comp (QuotientGroup.mk' (H.subgroupOf T))
  simpa [lambda, quotientCharacterInflation] using
    isBookIrreducibleCharacter_twistByCharacter lambda psi hpsi

public theorem degree_mul_left_eq_of_degree_one
    {G : Type*} [One G] (lambda psi : ClassFunction G)
    (hlambda : degree lambda = 1) :
    degree (lambda * psi) = degree psi := by
  change lambda 1 * psi 1 = psi 1
  change lambda 1 = 1 at hlambda
  rw [hlambda, one_mul]

public theorem proposition_1_7_twist_degree
    {G ι : Type*} [One G]
    (lambda : ι → ClassFunction G) (psi : ι → ClassFunction G) (i0 : ι)
    (htwist : ∀ i : ι, psi i = lambda i * psi i0)
    (hlambda_degree : ∀ i : ι, degree (lambda i) = 1) :
    ∀ i : ι, degree (psi i) = degree (psi i0) := by
  intro i
  rw [htwist i]
  exact degree_mul_left_eq_of_degree_one (lambda i) (psi i0) (hlambda_degree i)

public theorem degree_eq_of_subgroupRestriction_eq_smul_subgroupOf
    {G : Type*} [Group G] (H T : Subgroup G)
    (psi : ClassFunction T) (theta : ClassFunction H) (c : ℂ)
    (hres :
      subgroupRestriction (H.subgroupOf T) psi =
        c • subgroupOfClassFunction theta) :
    degree psi = c * degree theta := by
  have h := congrFun hres (1 : H.subgroupOf T)
  simpa [degree, subgroupRestriction, subgroupOfClassFunction] using h

public theorem scalarProduct_subgroupOfClassFunction
    {G : Type*} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T) (theta phi : ClassFunction H) :
    scalarProduct (H.subgroupOf T) (subgroupOfClassFunction theta)
        (subgroupOfClassFunction phi) =
      scalarProduct H theta phi := by
  classical
  let Hsub : Subgroup T := H.subgroupOf T
  letI : Fintype Hsub := Fintype.ofFinite Hsub
  let e := (Subgroup.subgroupOfEquivOfLe hHT).toEquiv
  have hcard : Nat.card Hsub = Nat.card H :=
    Nat.card_congr e
  have hsum :
      (∑ h : Hsub,
        subgroupOfClassFunction theta h * star (subgroupOfClassFunction phi h)) =
        ∑ h : H, theta h * star (phi h) := by
    simpa [Hsub, e, subgroupOfClassFunction] using
      (Equiv.sum_comp e (fun h : H => theta h * star (phi h)))
  unfold scalarProduct
  rw [hcard]
  exact congrArg (fun z => (Nat.card H : ℂ)⁻¹ * z) hsum

public theorem isCharacter_subgroupOfClassFunction_of_le
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T) (theta : ClassFunction H)
    (htheta : IsCharacter theta) :
    IsCharacter (subgroupOfClassFunction (T := T) theta) := by
  rcases htheta with ⟨V, _hadd, _hmod, _hfd, rho, htheta_eq⟩
  let e : (H.subgroupOf T) ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let rhoSub : Representation ℂ (H.subgroupOf T) V := rho.comp e.toMonoidHom
  refine ⟨V, inferInstance, inferInstance, inferInstance, rhoSub, ?_⟩
  funext h
  rw [htheta_eq]
  exact congrArg rho.character
    (show (⟨(h : T), h.2⟩ : H) = e h from Subtype.ext rfl)

public theorem isBookIrreducibleCharacter_subgroupOfClassFunction_of_le
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T) (theta : ClassFunction H)
    (htheta : IsBookIrreducibleCharacter theta) :
    IsBookIrreducibleCharacter (subgroupOfClassFunction (T := T) theta) := by
  refine ⟨isCharacter_subgroupOfClassFunction_of_le hHT theta htheta.1, ?_⟩
  rw [IsIrreducibleCharacter]
  rw [scalarProduct_subgroupOfClassFunction hHT theta theta]
  exact htheta.2

public theorem isBookIrreducibleCharacter_subgroupOfClassFunction_of_inertia
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta : IsBookIrreducibleCharacter theta) :
    IsBookIrreducibleCharacter
      (subgroupOfClassFunction (T := inertiaSubgroup H theta) theta) :=
  isBookIrreducibleCharacter_subgroupOfClassFunction_of_le
    (proposition_1_7_inertia_contains_H H theta htheta_class) theta htheta

public theorem scalarProduct_smul_subgroupOfClassFunction_irreducible
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H T : Subgroup G) [Finite H] [Finite T] (_hHT : H ≤ T)
    (theta : ClassFunction H)
    (thetaSubRep : Representation ℂ (H.subgroupOf T) V)
    (hthetaSub :
      subgroupOfClassFunction (T := T) theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (m : ℕ)
    (phi : ClassFunction (H.subgroupOf T))
    (phiRep : Representation ℂ (H.subgroupOf T) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep) :
    scalarProduct (H.subgroupOf T)
        ((m : ℂ) • subgroupOfClassFunction (T := T) theta) phi =
      if phi = subgroupOfClassFunction (T := T) theta then (m : ℂ) else 0 := by
  by_cases hphi_eq : phi = subgroupOfClassFunction (T := T) theta
  · rw [if_pos hphi_eq, hphi_eq]
    rw [scalarProduct_smul_left]
    have hnorm :
        scalarProduct (H.subgroupOf T)
          (subgroupOfClassFunction (T := T) theta)
          (subgroupOfClassFunction (T := T) theta) = 1 := by
      rw [hthetaSub]
      exact scalarProduct_representation_char_self thetaSubRep hthetaSub_irreducible
    rw [hnorm]
    simp
  · rw [if_neg hphi_eq]
    rw [scalarProduct_smul_left]
    rw [scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      (subgroupOfClassFunction (T := T) theta) phi thetaSubRep phiRep
      hthetaSub hphi hthetaSub_irreducible hphi_irreducible
      (fun h => hphi_eq h.symm)]
    simp

public theorem scalarProduct_smul_subgroupOfClassFunction_self
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H T : Subgroup G) [Finite H] [Finite T]
    (theta : ClassFunction H)
    (thetaSubRep : Representation ℂ (H.subgroupOf T) V)
    (hthetaSub :
      subgroupOfClassFunction (T := T) theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (m : ℕ) :
    scalarProduct (H.subgroupOf T)
        ((m : ℂ) • subgroupOfClassFunction (T := T) theta)
        (subgroupOfClassFunction (T := T) theta) =
      (m : ℂ) := by
  rw [scalarProduct_smul_left]
  have hnorm :
      scalarProduct (H.subgroupOf T)
        (subgroupOfClassFunction (T := T) theta)
        (subgroupOfClassFunction (T := T) theta) = 1 := by
    rw [hthetaSub]
    exact scalarProduct_representation_char_self thetaSubRep hthetaSub_irreducible
  rw [hnorm]
  simp

public theorem scalarProduct_restriction_subgroupOfClassFunction_eq_multiplicity_general
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction T)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) =
        if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (i : ι) :
    scalarProduct (H.subgroupOf T)
        (subgroupRestriction (H.subgroupOf T) (psi i))
        (subgroupOfClassFunction theta) =
      e i := by
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  let indTheta : ClassFunction T := inducedCF Hsub thetaSub
  have hi :
      scalarProduct T indTheta (psi i) = e i :=
    proposition_1_7_inertia_multiplicity_from_decomposition H T e psi theta
      horthT hdecompT i
  have hleftT :
      scalarProduct T (psi i) indTheta = e i := by
    have hstar :
        star (scalarProduct T (psi i) indTheta) = e i := by
      simpa [indTheta] using
        (scalarProduct_star_swap (G := T) indTheta (psi i)).trans hi
    have hstar' := congrArg star hstar
    simpa using hstar'
  rw [← inducedClassFunction_frobenius_right Hsub thetaSub (psi i) (hpsi_class i)]
  exact hleftT

public theorem scalarProduct_restriction_subgroupOfClassFunction_eq_multiplicity
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
        if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (i : ι) :
    scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i))
        (subgroupOfClassFunction theta) =
      e i :=
  scalarProduct_restriction_subgroupOfClassFunction_eq_multiplicity_general
    H (inertiaSubgroup H theta) theta e psi hpsi_class horthT hdecompT i

public theorem scalarProduct_restriction_eq_zero_of_ne_subgroupOfClassFunction
    {G ι V W : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (phi : ClassFunction (H.subgroupOf (inertiaSubgroup H theta)))
    (phiRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (thetaSubRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hthetaSub :
      subgroupOfClassFunction theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (hphi_ne : phi ≠ subgroupOfClassFunction theta)
    (i : ι) :
    scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i))
        phi = 0 := by
  classical
  let T : Subgroup G := inertiaSubgroup H theta
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  haveI : Hsub.Normal := subgroupOf_normal_of_normal H T
  have hnotConj :
      ∀ o : conjugateOrbitIndex Hsub thetaSubRep.character,
        phi ≠ conjugateOrbitConj Hsub thetaSubRep.character o := by
    intro o hphi_eq
    apply hphi_ne
    calc
      phi = conjugateOrbitConj Hsub thetaSubRep.character o := hphi_eq
      _ = thetaSubRep.character := by
          simpa [T, Hsub] using
            conjugateOrbitConj_subgroupOfClassFunction_of_inertia_rep
              H theta thetaSubRep hthetaSub o
      _ = subgroupOfClassFunction theta := hthetaSub.symm
  have htotal :
      scalarProduct T (inducedCF Hsub phi) (inducedCF Hsub thetaSub) = 0 := by
    have htotalRep :
        scalarProduct T (inducedCF Hsub phi)
            (inducedCF Hsub thetaSubRep.character) = 0 :=
      proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
        Hsub phi phiRep thetaSubRep hphi hphi_irreducible
        hthetaSub_irreducible hnotConj
    simpa [thetaSub, hthetaSub] using htotalRep
  have hweighted :
      scalarProduct T (inducedCF Hsub phi)
          (weightedFamilySum (fun i => (e i : ℂ)) psi) = 0 := by
    rw [← hdecompT]
    exact htotal
  have hsum :
      (∑ j : ι, (e j : ℂ) *
          scalarProduct T (inducedCF Hsub phi) (psi j)) = 0 := by
    have h := hweighted
    rw [scalarProduct_weightedFamilySum_right] at h
    simpa using h
  have hnat :
      ∀ j : ι,
        ∃ n : ℕ,
          scalarProduct T (inducedCF Hsub phi) (psi j) = (n : ℂ) := by
    intro j
    rcases isBookIrreducibleCharacter_representation_witness_irreducible
        (psi j) (hpsi_irreducible j) with
      ⟨Vj, _haddj, _hmodj, _hfdj, psiRep, hpsi_eq, _hpsi_irred⟩
    exact scalarProduct_inducedCF_representation_char_eq_nat
      Hsub phi (psi j) phiRep psiRep hphi hpsi_eq
  choose n hn using hnat
  have hsumNat :
      (∑ j : ι, (e j : ℂ) * (n j : ℂ)) = 0 := by
    simpa [hn] using hsum
  have hni : n i = 0 :=
    nat_weighted_complex_sum_eq_zero_component e n he_pos i hsumNat
  have hinnerT :
      scalarProduct T (inducedCF Hsub phi) (psi i) = 0 := by
    rw [hn i, hni]
    norm_num
  have hinnerH :
      scalarProduct Hsub phi (subgroupRestriction Hsub (psi i)) = 0 := by
    rw [← inducedClassFunction_frobenius_general Hsub phi (psi i) (hpsi_class i)]
    exact hinnerT
  have hstar := congrArg star hinnerH
  simpa [scalarProduct_star_swap (G := Hsub)
      (subgroupRestriction Hsub (psi i)) phi] using hstar

public theorem clifford_restriction_inner_eq_of_ne_subgroupOfClassFunction
    {G ι V W : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (phi : ClassFunction (H.subgroupOf (inertiaSubgroup H theta)))
    (phiRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (thetaSubRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hthetaSub :
      subgroupOfClassFunction theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (hphi_ne : phi ≠ subgroupOfClassFunction theta)
    (i : ι) :
    scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i))
        phi =
      scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        ((e i : ℂ) • subgroupOfClassFunction theta) phi := by
  classical
  let T : Subgroup G := inertiaSubgroup H theta
  have hHT : H ≤ T :=
    proposition_1_7_inertia_contains_H H theta htheta_class
  have hpsi_class : ∀ i : ι, IsClassFunction (psi i) := fun j =>
    isBookIrreducibleCharacter_isClassFunction (psi j) (hpsi_irreducible j)
  rw [scalarProduct_restriction_eq_zero_of_ne_subgroupOfClassFunction
      H theta e psi he_pos hpsi_class hpsi_irreducible hdecompT
      phi phiRep thetaSubRep hphi hphi_irreducible
      hthetaSub hthetaSub_irreducible hphi_ne i]
  rw [scalarProduct_smul_subgroupOfClassFunction_irreducible
      H T hHT theta thetaSubRep hthetaSub hthetaSub_irreducible (e i)
      phi phiRep hphi hphi_irreducible]
  simp [hphi_ne]

public theorem clifford_restriction_inner_eq_of_inertia_decomposition_of_orthogonal
    {G ι V W : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
        if i = j then 1 else 0)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (phi : ClassFunction (H.subgroupOf (inertiaSubgroup H theta)))
    (phiRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (thetaSubRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hthetaSub :
      subgroupOfClassFunction theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (i : ι) :
    scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i))
        phi =
      scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        ((e i : ℂ) • subgroupOfClassFunction theta) phi := by
  classical
  by_cases hphi_eq :
      phi = subgroupOfClassFunction (T := inertiaSubgroup H theta) theta
  · rw [hphi_eq]
    let T : Subgroup G := inertiaSubgroup H theta
    rw [scalarProduct_restriction_subgroupOfClassFunction_eq_multiplicity_general
        H T theta e psi hpsi_class horthT hdecompT i]
    exact (scalarProduct_smul_subgroupOfClassFunction_self
      H T theta thetaSubRep hthetaSub hthetaSub_irreducible (e i)).symm
  · exact clifford_restriction_inner_eq_of_ne_subgroupOfClassFunction
      H theta htheta_class e psi he_pos hpsi_irreducible hdecompT
      phi phiRep thetaSubRep hphi hphi_irreducible
      hthetaSub hthetaSub_irreducible hphi_eq i

public theorem clifford_restriction_of_inertia_decomposition_of_orthogonal
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
        if i = j then 1 else 0)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi) :
    ∀ i : ι,
      subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i) =
        (e i : ℂ) • subgroupOfClassFunction theta := by
  classical
  intro i
  let T : Subgroup G := inertiaSubgroup H theta
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  have hthetaSub_book :
      IsBookIrreducibleCharacter thetaSub :=
    isBookIrreducibleCharacter_subgroupOfClassFunction_of_inertia H theta
      htheta_class htheta_irreducible
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      thetaSub hthetaSub_book with
    ⟨Vθ, _haddθ, _hmodθ, _hfdθ, thetaSubRep, hthetaSub, hthetaSub_irred⟩
  have hres_class :
      IsClassFunction (subgroupRestriction Hsub (psi i)) :=
    subgroupRestriction_isClassFunction_of_isClassFunction Hsub (psi i) (hpsi_class i)
  have hrhs_class :
      IsClassFunction ((e i : ℂ) • thetaSub) :=
    isClassFunction_smul (e i : ℂ) thetaSub
      (isBookIrreducibleCharacter_isClassFunction thetaSub hthetaSub_book)
  apply classFunction_eq_of_inner_irreducible
      (subgroupRestriction Hsub (psi i)) ((e i : ℂ) • thetaSub)
      hres_class hrhs_class
  intro chi hchi
  rcases representation_irreducibleCharacter_witness_irreducible chi hchi with
    ⟨nχ, phiRep, hphi, hphi_irred⟩
  have hphiCF : ofConjClassFunction chi = phiRep.character := by
    rw [hphi]
    exact ofConjClassFunction_characterClassFunction phiRep
  rw [representation_inner_toConjClassFunction_right
    (subgroupRestriction Hsub (psi i)) hres_class chi]
  rw [representation_inner_toConjClassFunction_right
    ((e i : ℂ) • thetaSub) hrhs_class chi]
  exact clifford_restriction_inner_eq_of_inertia_decomposition_of_orthogonal
    H theta htheta_class e psi he_pos hpsi_class horthT hpsi_irreducible hdecompT
    (ofConjClassFunction chi) phiRep thetaSubRep hphiCF hphi_irred
    hthetaSub hthetaSub_irred i

public theorem proposition_1_7_multiplicity_eq_of_restriction_eq_smul
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (i : ι) (m : ℕ)
    (hclass_i : IsClassFunction (psi i))
    (htheta_irreducible : IsIrreducibleCharacter theta)
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hres :
      subgroupRestriction (H.subgroupOf T) (psi i) =
        (m : ℂ) • subgroupOfClassFunction theta) :
    e i = m := by
  have hi := proposition_1_7_inertia_multiplicity_from_decomposition
    H T e psi theta horthT hdecompT i
  have hC : (e i : ℂ) = (m : ℂ) := by
    rw [← hi]
    rw [inducedClassFunction_frobenius_general (H.subgroupOf T)
      (subgroupOfClassFunction theta) (psi i) hclass_i]
    rw [hres]
    rw [scalarProduct_smul_right]
    rw [scalarProduct_subgroupOfClassFunction hHT theta theta]
    rw [show star (m : ℂ) = (m : ℂ) by simp]
    rw [htheta_irreducible]
    ring
  exact_mod_cast hC

public theorem proposition_1_7_multiplicity_one_of_restriction_eq_theta
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (i : ι)
    (hclass_i : IsClassFunction (psi i))
    (htheta_irreducible : IsIrreducibleCharacter theta)
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hres :
      subgroupRestriction (H.subgroupOf T) (psi i) =
        subgroupOfClassFunction theta) :
    e i = 1 := by
  exact proposition_1_7_multiplicity_eq_of_restriction_eq_smul H T hHT
    e psi theta i 1 hclass_i htheta_irreducible horthT hdecompT
    (by simpa using hres)

/-! ## Proposition (1.7): arithmetic consequences of the Clifford data -/

public theorem scalarProduct_irreducible_representationCharacter_family
    {G ι : Type*} [Group G] [Finite G] [DecidableEq ι]
    {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (chi : ι → ClassFunction G)
    (rho : ∀ i : ι, Representation ℂ G (V i))
    (hchi : ∀ i : ι, chi i = (rho i).character)
    (hirr : ∀ i : ι, Representation.IsIrreducible (rho i))
    (hdistinct : Pairwise fun i j => chi i ≠ chi j) :
    ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [hchi i, scalarProduct_representation_char_self (rho i) (hirr i)]
  · have hne : chi i ≠ chi j := hdistinct hij
    have hchars_ne : (rho i).character ≠ (rho j).character := by
      intro hchars
      apply hne
      rw [hchi i, hchi j, hchars]
    letI : Representation.IsIrreducible (rho i) := hirr i
    letI : Representation.IsIrreducible (rho j) := hirr j
    simp [hij, hchi i, hchi j,
      scalarProduct_representation_char_eq_zero_of_ne (rho i) (rho j) hchars_ne]

/--
Peterfalvi (1.7)(a), in the arithmetic form supplied by Clifford
correspondence: the induced characters are distinct irreducibles and the
induced character decomposes with the same multiplicities.
-/
public theorem proposition_1_7_a_arithmetic
    {G ι : Type*} [Finite G] [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (indGHtheta : ClassFunction G)
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsIrreducibleCharacter (chi i)) ∧
      indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
  refine ⟨?_, ?_, hdecomp⟩
  · intro i j hij hchi
    have hcross := horth i j
    have hself := horth i i
    rw [hchi] at hcross
    rw [hchi] at hself
    simp [hij] at hcross
    simp at hself
    rw [hcross] at hself
    norm_num at hself
  · intro i
    simpa [IsIrreducibleCharacter] using horth i i

public theorem proposition_1_7_a_from_irreducible_representation_characters
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (indGHtheta : ClassFunction G)
    (rho : ∀ i : ι, Representation ℂ G (V i))
    (hchi : ∀ i : ι, chi i = (rho i).character)
    (hirr : ∀ i : ι, Representation.IsIrreducible (rho i))
    (hdistinct : Pairwise fun i j => chi i ≠ chi j)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsIrreducibleCharacter (chi i)) ∧
      indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi :=
  proposition_1_7_a_arithmetic e chi indGHtheta
    (scalarProduct_irreducible_representationCharacter_family chi rho hchi hirr hdistinct)
    hdecomp

public theorem proposition_1_7_a_from_induced_orthonormal_characters
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (indGHtheta : ClassFunction G)
    (hchi_character : ∀ i : ι, IsCharacter (chi i))
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsBookIrreducibleCharacter (chi i)) ∧
      indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
  rcases proposition_1_7_a_arithmetic e chi indGHtheta horth hdecomp with
    ⟨hdistinct, hirr, hdecomp'⟩
  exact ⟨hdistinct, fun i => ⟨hchi_character i, hirr i⟩, hdecomp'⟩

end Section1
