module

public import Theory.Representation.SymplecticNatural.CubicFixedSpace
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# The concrete six-letter and binary symplectic natural modules

The coordinate map sends the characteristic vector of each duad to its
existing polar vector. It kills the constant line. Every even binary word
of length six is zero, constant, a duad, or the complement of a duad; this
small kernel-checked table proves that the induced map on the actual deleted
quotient is bijective and respects every permutation. The existing faithful
polar representation is surjective by the symplectic order formula. Its
restriction identifies A₆ with the actual commutator subgroup Sp₄(2)'.

These are concrete linear and group equivalences, with compatible forward
maps, for the natural-action identification used in Aschbacher–Smith B.4.2(3)
and B.5.1(2),(5), printed pp.86,99,102–103. The duad coordinates come from
`Theory.SpecificGroups.SymmetricSix.Parabolics` (I.5, printed pp.419–422).
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation
open scoped Matrix
namespace Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison

private def coordinates : Full (Fin 6) →ₗ[ZMod 2] NaturalModule where
  toFun v := vec (v 4 + v 5) (v 2 + v 3 + v 4 + v 5) (v 3 + v 5)
    (v 1 + v 3 + v 4 + v 5)
  map_add' v w := by ext i; cases i <;> simp [vec] <;> split <;> ring
  map_smul' c v := by ext i; cases i <;> simp [vec] <;> split <;> ring

private def duadWord (d : Duad) : Full (Fin 6) := fun i => if i ∈ duadSet d then 1 else 0

private theorem coordinates_duad (d : Duad) : coordinates (duadWord d) = (polarVector d).val := by
  decide +revert +kernel

private theorem coordinates_constant : coordinates (allOne (Fin 6)) = 0 := by decide +kernel

private theorem core_classification (v : Full (Fin 6)) (hv : ∑ i, v i = 0) :
    v = 0 ∨ v = allOne (Fin 6) ∨ ∃ d, v = duadWord d ∨ v = allOne (Fin 6) + duadWord d := by
  decide +revert +kernel

private theorem duadWord_core (d : Duad) : duadWord d ∈ core (Fin 6) := by
  change ∑ i, duadWord d i = 0
  decide +revert +kernel

private theorem duadWord_permute (g : S6) (d : Duad) :
    representation (Fin 6) g (duadWord d) = duadWord (g • d) := by
  ext i
  simp [duadWord, duadSet_smul, ← Equiv.eq_symm_apply]


private theorem constants_le_ker : constants (Fin 6) ≤ coordinates.ker := by
  rw [constants, Submodule.span_le, Set.singleton_subset_iff]
  exact coordinates_constant

private noncomputable def naturalCoordinates : natural (Fin 6) →ₗ[ZMod 2] NaturalModule :=
  ((constants (Fin 6)).liftQ coordinates constants_le_ker).comp (natural (Fin 6)).subtype

@[simp] private theorem naturalCoordinates_core (v : core (Fin 6)) :
    naturalCoordinates (coreToNatural (Fin 6) v) = coordinates v.val := rfl

private theorem coordinates_ker_core (v : Full (Fin 6)) (hv : v ∈ core (Fin 6))
    (hz : coordinates v = 0) : v ∈ constants (Fin 6) := by
  rcases core_classification v hv with rfl | rfl | ⟨d, rfl | rfl⟩
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span (Set.mem_singleton _)
  · exact False.elim ((polarVector d).property ((coordinates_duad d).symm.trans hz))
  · rw [map_add, coordinates_constant, zero_add, coordinates_duad] at hz
    exact False.elim ((polarVector d).property hz)

private theorem naturalCoordinates_injective : Function.Injective naturalCoordinates := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  have hz : coordinates a.val = 0 := hv
  have ha := coordinates_ker_core a.val a.property hz
  have hq : coreToNatural (Fin 6) a = 0 := by
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr ha
  exact hq

private theorem naturalCoordinates_surjective : Function.Surjective naturalCoordinates := by
  intro v
  by_cases hz : v = 0
  · exact ⟨0, by simp [hz]⟩
  obtain ⟨d, hd⟩ := polarVector_bijective.surjective ⟨v, hz⟩
  refine ⟨coreToNatural (Fin 6) ⟨duadWord d, duadWord_core d⟩, ?_⟩
  rw [naturalCoordinates_core, coordinates_duad]
  exact congrArg Subtype.val hd

/-- The deleted six-letter quotient in the standard binary symplectic coordinates. -/
noncomputable def naturalLinearEquiv : natural (Fin 6) ≃ₗ[ZMod 2] NaturalModule :=
  LinearEquiv.ofBijective naturalCoordinates
    ⟨naturalCoordinates_injective, naturalCoordinates_surjective⟩

private theorem coordinates_equivariant (g : S6) (v : Full (Fin 6))
    (hv : v ∈ core (Fin 6)) :
    coordinates (representation (Fin 6) g v) =
      (polarRepresentation g).val *ᵥ coordinates v := by
  rcases core_classification v hv with rfl | rfl | ⟨d, rfl | rfl⟩
  · simp
  · rw [permute_allOne, coordinates_constant, Matrix.mulVec_zero]
  · rw [duadWord_permute, coordinates_duad, coordinates_duad,
      polarRepresentation_equivariant]
  · rw [map_add, permute_allOne, map_add, coordinates_constant, zero_add,
      map_add, coordinates_constant, zero_add, duadWord_permute,
      coordinates_duad, coordinates_duad, polarRepresentation_equivariant]

theorem naturalLinearEquiv_equivariant (g : S6) (v : natural (Fin 6)) :
    naturalLinearEquiv (naturalRepresentation (Fin 6) g v) =
      (polarRepresentation g).val *ᵥ naturalLinearEquiv v := by
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  rw [← coreToNatural_equivariant]
  exact coordinates_equivariant g a.val a.property

theorem polarRepresentation_bijective : Function.Bijective polarRepresentation := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨polarRepresentation_injective, ?_⟩
  have hc := Theory.SpecificGroups.SymplecticFour.card_sp (ZMod 2)
  norm_num [Nat.card_eq_fintype_card, ZMod.card] at hc
  change Nat.card S6 = Nat.card (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2))
  rw [hc]
  norm_num [S6, Letter, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The full polar representation is the concrete exceptional isomorphism S₆ ≃ Sp₄(2). -/
@[expose] noncomputable def symmetricSymplecticEquiv : S6 ≃* Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective polarRepresentation polarRepresentation_bijective

open Representation.SymplecticCubicFixedSpace in
theorem alternatingDerivedPolar_surjective : Function.Surjective alternatingDerivedPolar := by
  have hm : (commutator S6).map polarRepresentation =
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr polarRepresentation_bijective.surjective,
      commutator_def]
  intro g
  have hg : g.val ∈ (commutator S6).map polarRepresentation := hm.symm ▸ g.property
  obtain ⟨a, ha, he⟩ := hg
  rw [alternatingGroup.commutator_perm_eq (by norm_num [Letter])] at ha
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

/-- Restriction of the same polar isomorphism to the actual commutator groups. -/
@[expose] noncomputable def alternatingDerivedEquiv :
    alternatingGroup (Fin 6) ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) :=
  MulEquiv.ofBijective Representation.SymplecticCubicFixedSpace.alternatingDerivedPolar
    ⟨Representation.SymplecticCubicFixedSpace.alternatingDerivedPolar_injective,
      alternatingDerivedPolar_surjective⟩

end Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison
