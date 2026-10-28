module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ChevalleyVersions
public import Theory.AlgebraicGroup.RootSystems.F4RootLattice
public import Theory.AlgebraicGroup.RootSystems.F4RootPairingULift
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter

/-!
# Actual F4 characters from the integral root lattice

The equality of the standard F4 root and weight lattices gives actual characters
of any algebraic-group root model: each root is an actual torus character, and
multiplication and inversion realize sums and negatives of integral weights.
Closure induction therefore realizes every integral weight by a character in
the actual torus root lattice, with its pairing against every coroot verified.

In particular, evaluation on the four coroots of the displayed standard base is
surjective onto `Fin 4 → ℤ`. These roots need not be the model's originally
chosen positive base; the final indexing lemma identifies their indices in the
standard pairing. Injectivity of this evaluation requires semisimple geometry and
is retained explicitly in the root-lattice equality theorem below.

Sources: GLS3, Sections 1.9 and 1.12, and Proposition 1.14.1; the integral F4
calculation is `StandardRootSystem.typeF4_rootLattice_eq_weightLattice`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem

universe u

namespace Theory.AlgebraicGroup.RootSystemModel

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Identify actual roots with the standard F4 roots, forgetting the universe lift. -/
noncomputable def f4RootIndex (M : RootSystemModel typeF4RootPairingULift G) :
    M.rootData.Root ≃ typeF4Roots :=
  M.rootEquiv.trans typeF4RootPairingULiftEquiv.indexEquiv

omit [IsAlgClosed k] in
lemma f4_pairing_eq (M : RootSystemModel typeF4RootPairingULift G)
    (α β : M.rootData.Root) :
    M.rootData.pairing α β = typeF4RootPairing.pairingIn ℤ
      (f4RootIndex M α) (f4RootIndex M β) := by
  apply (Int.cast_injective : Function.Injective (fun n : ℤ => (n : ℝ)))
  rw [M.actual.1 α β]
  exact (typeF4RootPairingULiftEquiv.pairing_eq (M.rootEquiv α)
    (M.rootEquiv β)).symm.trans
      (typeF4RootPairing.algebraMap_pairingIn ℤ _ _).symm

/-- Every integral F4 weight is the coroot evaluation of an actual root-lattice character. -/
theorem f4_exists_rootLattice_character (M : RootSystemModel typeF4RootPairingULift G)
    (f : typeF4WeightModule) :
    ∃ χ : TorusWeight M.torus, χ ∈ TorusRootLattice M.torus ∧ ∀ β : M.rootData.Root,
      M.rootData.weightPairing χ β =
        f (typeF4RootPairing.corootSpanMem ℤ (f4RootIndex M β)) := by
  have hf : f ∈ typeF4RootLattice := by
    rw [typeF4_rootLattice_eq_weightLattice]
    trivial
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨α, rfl⟩ := hf
    refine ⟨M.rootData.rootWeight ((f4RootIndex M).symm α), ?_, ?_⟩
    · apply Subgroup.subset_closure
      rw [← M.realization.2.1]
      exact Set.mem_range_self _
    intro β
    rw [M.realization.weightPairing_rootWeight, f4_pairing_eq]
    simp [typeF4RootWeight]
  | zero =>
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro β
    rw [M.realization.weightPairing_one]
    rfl
  | add f g hf hg ihf ihg =>
    obtain ⟨χ, hχmem, hχ⟩ := ihf
    obtain ⟨ψ, hψmem, hψ⟩ := ihg
    refine ⟨χ * ψ, Subgroup.mul_mem _ hχmem hψmem, ?_⟩
    intro β
    rw [M.realization.weightPairing_mul, hχ, hψ]
    rfl
  | neg f hf ih =>
    obtain ⟨χ, hχmem, hχ⟩ := ih
    refine ⟨χ⁻¹, Subgroup.inv_mem _ hχmem, ?_⟩
    intro β
    rw [M.realization.weightPairing_inv, hχ]
    rfl

/-- The actual root indexed by a member of the displayed standard F4 base. -/
noncomputable def f4SimpleRoot (M : RootSystemModel typeF4RootPairingULift G)
    (i : Fin 4) : M.rootData.Root :=
  (f4RootIndex M).symm (typeF4RootPairing_baseEquiv i)

/-- Arbitrary integral coordinates on the four coroots come from root-lattice characters. -/
theorem f4_exists_rootLattice_character_coordinates
    (M : RootSystemModel typeF4RootPairingULift G) (z : Fin 4 → ℤ) :
    ∃ χ : TorusWeight M.torus, χ ∈ TorusRootLattice M.torus ∧ ∀ i,
      M.rootData.weightPairing χ (f4SimpleRoot M i) = z i := by
  let e : typeF4RootPairing_base.flip.support ≃ typeF4RootPairing_base.support :=
    Equiv.subtypeEquivRight (fun _ => by rw [RootPairing.Base.flip_support])
  let b := typeF4RootPairing_base.flip.toWeightBasisInt.reindex
    (e.trans typeF4RootPairing_baseEquiv.symm)
  let f : typeF4WeightModule := b.constr ℤ z
  obtain ⟨χ, hχmem, hχ⟩ := f4_exists_rootLattice_character M f
  refine ⟨χ, hχmem, ?_⟩
  intro i
  rw [hχ]
  have hcoroot : typeF4RootPairing.corootSpanMem ℤ
      (f4RootIndex M (f4SimpleRoot M i)) =
      b i := by
    dsimp only [b]
    rw [Module.Basis.reindex_apply]
    apply Subtype.ext
    rw [RootPairing.Base.coe_toWeightBasisInt_apply]
    simp only [f4SimpleRoot, Equiv.apply_symm_apply]
    rfl
  rw [hcoroot]
  exact b.constr_basis ℤ z i

/-- Evaluation of the actual character lattice on the four standard coroots. -/
noncomputable def f4CorootCoordinates (M : RootSystemModel typeF4RootPairingULift G) :
    Additive (TorusWeight M.torus) →+ (Fin 4 → ℤ) where
  toFun χ i := M.rootData.characterCorootPairing (f4SimpleRoot M i) χ
  map_zero' := by ext i; exact map_zero _
  map_add' χ ψ := by ext i; exact map_add _ χ ψ

lemma f4CorootCoordinates_apply (M : RootSystemModel typeF4RootPairingULift G)
    (χ : TorusWeight M.torus) (i : Fin 4) :
    f4CorootCoordinates M (Additive.ofMul χ) i =
      M.rootData.weightPairing χ (f4SimpleRoot M i) :=
  (M.realization.weightPairing_eq_characterCorootPairing χ _).symm

/-- Unimodularity of the F4 root lattice makes coroot evaluation surjective. -/
theorem f4CorootCoordinates_surjective (M : RootSystemModel typeF4RootPairingULift G) :
    Function.Surjective (f4CorootCoordinates M) := by
  intro z
  obtain ⟨χ, _, hχ⟩ := f4_exists_rootLattice_character_coordinates M z
  exact ⟨Additive.ofMul χ, funext fun i => (f4CorootCoordinates_apply M χ i).trans (hχ i)⟩

/-- Character separation upgrades the weight realization to equality of the actual lattices. -/
theorem f4_rootLattice_eq_top_of_corootCoordinates_injective
    (M : RootSystemModel typeF4RootPairingULift G)
    (hinj : Function.Injective (f4CorootCoordinates M)) :
    TorusRootLattice M.torus = ⊤ := by
  apply top_unique
  intro χ _
  obtain ⟨ψ, hψmem, hψ⟩ := f4_exists_rootLattice_character_coordinates M
    (f4CorootCoordinates M (Additive.ofMul χ))
  have heq : Additive.ofMul ψ = Additive.ofMul χ := by
    apply hinj
    funext i
    exact (f4CorootCoordinates_apply M ψ i).trans (hψ i)
  have heq' : ψ = χ := congrArg Additive.toMul heq
  rw [← heq']
  exact hψmem

omit [IsAlgClosed k] in
theorem f4SimpleRoot_rootIndex (M : RootSystemModel typeF4RootPairingULift G) (i : Fin 4) :
    f4RootIndex M (f4SimpleRoot M i) = typeF4RootPairing_baseEquiv i := by
  rw [f4SimpleRoot, Equiv.apply_symm_apply]


end Theory.AlgebraicGroup.RootSystemModel
