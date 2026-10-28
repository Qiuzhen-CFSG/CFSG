module

public import Theory.Character.Peterfalvi1.MackeyCore
public import Theory.Character.CharacterValues
public import Theory.Character.Orthogonality

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace Section3
universe u v

public theorem ofConjClassFunction_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.ofConjClassFunction χ) := by
  classical
  rcases hχ with ⟨hchar, hirrNorm⟩
  rcases hchar with ⟨n, ρ, hχeq⟩
  refine ⟨n, ρ, ?_, ?_⟩
  · apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hχeq] using hirrNorm
  · rw [hχeq]
    exact Section1.ofConjClassFunction_characterClassFunction ρ

private theorem scalarProduct_evalCoeff_eq_coeffDot
    {G ι : Type*} [Finite G] [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (horth : ∀ i j, Section1.scalarProduct G (μ i) (μ j) = if i = j then 1 else 0)
    (v w : Section1.CoeffVector ι) :
    Section1.scalarProduct G (Section1.evalCoeff μ v) (Section1.evalCoeff μ w) =
      (Section1.coeffDot v w : ℂ) := by
  classical
  have hleft :
      (∑ j : ι, (v j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((v j : ℂ) • μ j) g) := by
    ext g
    simp
  have hright :
      (∑ j : ι, (w j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) := by
    ext g
    simp
  simp only [Section1.evalCoeff]
  rw [hleft, hright]
  rw [Section1.scalarProduct_fintype_sum_left]
  simp_rw [Section1.scalarProduct_smul_left]
  change ∑ i : ι, (v i : ℂ) *
      Section1.scalarProduct G (μ i) (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) =
    ((∑ i : ι, v i * w i : ℤ) : ℂ)
  rw [show ((∑ i : ι, v i * w i : ℤ) : ℂ) =
      ∑ i : ι, ((v i * w i : ℤ) : ℂ) by simp]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Section1.scalarProduct_fintype_sum_right]
  simp_rw [Section1.scalarProduct_smul_right]
  calc
    (v i : ℂ) * (∑ x : ι, star (w x : ℂ) *
        Section1.scalarProduct G (μ i) (μ x)) =
        (v i : ℂ) * (w i : ℂ) := by
          simp [horth]
    _ = (v i * w i : ℤ) := by
          simp [Int.cast_mul]


public theorem irreducibleBasis_scalarProduct_evalCoeff
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (v w : Section1.CoeffVector ι) :
    Section1.scalarProduct G
        (Section1.evalCoeff (fun i => Section1.ofConjClassFunction (χ i)) v)
        (Section1.evalCoeff (fun i => Section1.ofConjClassFunction (χ i)) w) =
      (Section1.coeffDot v w : ℂ) := by
  classical
  exact scalarProduct_evalCoeff_eq_coeffDot
    (fun i => Section1.ofConjClassFunction (χ i))
    (by
      intro i j
      calc
        Section1.scalarProduct G
            (Section1.ofConjClassFunction (χ i))
            (Section1.ofConjClassFunction (χ j)) =
            classFunctionInner (χ i) (χ j) := by
              symm
              simpa [Section1.toConjClassFunction_ofConjClassFunction] using
                (Section1.classFunctionInner_toConjClassFunction
                  (Section1.ofConjClassFunction (χ i))
                  (Section1.ofConjClassFunction (χ j))
                  (Section1.ofConjClassFunction_isClassFunction (χ i))
                  (Section1.ofConjClassFunction_isClassFunction (χ j)))
        _ = if i = j then 1 else 0 := by
              exact Section1.representation_completeFamily_orthonormal hχ i j)
    v w

@[expose] public noncomputable def irreducibleBasisCoeff
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    {χ : ι → ConjClassFunction G}
    (φ : Section1.ClassFunction G)
    (hint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) = (z : ℂ)) :
    Section1.CoeffVector ι :=
  fun i => Classical.choose (hint i)

public theorem irreducibleBasisCoeff_spec
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    {χ : ι → ConjClassFunction G}
    (φ : Section1.ClassFunction G)
    (hint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) = (z : ℂ))
    (i : ι) :
    Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) =
      (irreducibleBasisCoeff φ hint i : ℂ) := by
  exact Classical.choose_spec (hint i)

public theorem irreducibleBasis_evalCoeff_coeff
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (ConjClassFunction G))
    (hb : ∀ i, b i = χ i)
    (φ : Section1.ClassFunction G) (hφ : Section1.IsClassFunction φ)
    (hint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) = (z : ℂ)) :
    Section1.evalCoeff (fun i => Section1.ofConjClassFunction (χ i))
        (irreducibleBasisCoeff φ hint) = φ := by
  classical
  let Φ : ConjClassFunction G := Section1.toConjClassFunction φ hφ
  have hrepr :
      ∀ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) = b.repr Φ i := by
    intro i
    calc
      (irreducibleBasisCoeff φ hint i : ℂ) =
          Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) := by
            exact (irreducibleBasisCoeff_spec φ hint i).symm
      _ = classFunctionInner Φ (χ i) := by
            symm
            exact Section1.representation_inner_toConjClassFunction_right φ hφ (χ i)
      _ = b.repr Φ i := by
            exact (Section1.representation_basis_repr_eq_inner hχ b hb Φ i).symm
  have hsum :
      (∑ i : ι, b.repr Φ i • χ i) = Φ := by
    calc
      (∑ i : ι, b.repr Φ i • χ i) =
          ∑ i : ι, b.repr Φ i • b i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hb i]
      _ = Φ := Module.Basis.sum_repr b Φ
  ext g
  simp only [Section1.evalCoeff]
  rw [show (∑ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) •
        Section1.ofConjClassFunction (χ i)) g =
      ∑ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) *
        Section1.ofConjClassFunction (χ i) g by simp]
  calc
    (∑ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) *
        Section1.ofConjClassFunction (χ i) g) =
        ∑ i : ι, b.repr Φ i * Section1.ofConjClassFunction (χ i) g := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hrepr i]
    _ = φ g := by
          have hg := congrFun hsum (ConjClasses.mk g)
          simpa [Φ, Section1.ofConjClassFunction, smul_eq_mul,
            Section1.toConjClassFunction_apply] using hg


public theorem degree_ne_zero_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G] (χ : Section1.ClassFunction G)
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.degree χ ≠ 0 := by
  classical
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  intro hdeg
  have hfinC : (Module.finrank ℂ (Fin n → ℂ) : ℂ) = 0 := by
    simpa [Section1.degree_representation_character ρ] using hdeg
  have hfin : Module.finrank ℂ (Fin n → ℂ) = 0 := by
    exact_mod_cast hfinC
  have hsub : Subsingleton (Fin n → ℂ) := Module.finrank_zero_iff.mp hfin
  let : Representation.IsIrreducible ρ := hρ
  have hntriv : Nontrivial (Fin n → ℂ) := by
    by_contra hV
    have hsub' : Subsingleton (Fin n → ℂ) := not_nontrivial_iff_subsingleton.mp hV
    have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      change (⊥ : Submodule ℂ (Fin n → ℂ)) = ⊤
      rw [eq_top_iff]
      intro v _hv
      simp [hsub'.elim v 0]
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ) hbot_top
  by_cases hn : n = 0
  · subst n
    exact (not_subsingleton (Fin 0 → ℂ)) hsub
  · have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    let a : Fin n := Classical.choice inferInstance
    have hzero_one : (0 : Fin n → ℂ) = 1 := hsub.elim _ _
    have hcontr : (0 : Fin n → ℂ) a = (1 : Fin n → ℂ) a :=
      congrFun hzero_one a
    norm_num at hcontr

public theorem isVirtualCharacter_principalCharacter
    {G : Type u} [Group G] [Finite G] :
    IsVirtualCharacter (Section1.principalCharacter G) := by
  classical
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => 1),
    (fun _ : Fin 1 => Representation.trivial ℂ G (Fin 1 → ℂ)), ?_⟩
  ext g
  simp [virtualCharacterOfRepresentations, Section1.principalCharacter,
    Representation.character]

set_option backward.isDefEq.respectTransparency false in
public theorem principalCharacter_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G] :
    Section1.IsIrreducibleCharacterOnGroup (Section1.principalCharacter G) := by
  classical
  let ρ : Representation ℂ G (Fin 1 → ℂ) := Representation.trivial ℂ G (Fin 1 → ℂ)
  refine ⟨1, ρ, ?_, ?_⟩
  · rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ G)
      (V := ρ.asModule)
      (by change Module.finrank ℂ (Fin 1 → ℂ) = 1; simp)
  · ext g
    simp [ρ, Section1.principalCharacter, Representation.character]

public theorem isVirtualCharacter_of_irreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G] {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    IsVirtualCharacter χ := by
  classical
  change ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
    Representation.IsIrreducible ρ ∧ χ = ρ.character at hχ
  rcases hχ with ⟨n, ρ, _hirr, hχeq⟩
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => n),
    (fun _ : Fin 1 => ρ), ?_⟩
  ext g
  simp [virtualCharacterOfRepresentations, hχeq]

private theorem character_cast_nat
    {G : Type*} [Group G] {n m : ℕ} (h : n = m)
    (ρ : Representation ℂ G (Fin n → ℂ)) (g : G) :
    Representation.character
        (cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) h) ρ) g =
      ρ.character g := by
  subst m
  simp [Representation.character]

public theorem isVirtualCharacter_add
    {G : Type u} [Group G] {χ ψ : G → ℂ}
    (hχ : IsVirtualCharacter χ)
    (hψ : IsVirtualCharacter ψ) :
    IsVirtualCharacter (χ + ψ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  let mrs : Fin (r + s) → ℤ := Fin.addCases m m'
  let nrs : Fin (r + s) → ℕ := Fin.addCases n n'
  have hn_left (i : Fin r) : n i = nrs (Fin.castAdd s i) := by
    simp [nrs, Fin.addCases_left]
  have hn_right (j : Fin s) : n' j = nrs (Fin.natAdd r j) := by
    simp [nrs, Fin.addCases_right]
  let ρrs : (i : Fin (r + s)) → Representation ℂ G (Fin (nrs i) → ℂ) :=
    Fin.addCases
      (motive := fun i => Representation ℂ G (Fin (nrs i) → ℂ))
      (fun i =>
        cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) (hn_left i))
          (ρ i))
      (fun j =>
        cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) (hn_right j))
          (σ j))
  refine ⟨r + s, mrs, nrs, ρrs, ?_⟩
  ext g
  simp only [Pi.add_apply, virtualCharacterOfRepresentations,
    mrs, nrs, ρrs, Fin.sum_univ_add]
  simp [Fin.addCases_left, Fin.addCases_right, character_cast_nat]

public theorem isVirtualCharacter_neg
    {G : Type u} [Group G] {χ : G → ℂ}
    (hχ : IsVirtualCharacter χ) :
    IsVirtualCharacter (-χ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  refine ⟨r, fun i => -m i, n, ρ, ?_⟩
  ext g
  simp [virtualCharacterOfRepresentations]

public theorem isVirtualCharacter_sub
    {G : Type u} [Group G] {χ ψ : G → ℂ}
    (hχ : IsVirtualCharacter χ)
    (hψ : IsVirtualCharacter ψ) :
    IsVirtualCharacter (χ - ψ) := by
  simpa [sub_eq_add_neg] using isVirtualCharacter_add hχ (isVirtualCharacter_neg hψ)


end Section3
