module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry

/-!
# Assembling the point orbits and source radical geometry

The independent parabolic, orbit and fixed-space calculations meet at the
proved equality R₆ = O₂(L₆T) = shearSubgroup. We use that equality to identify
the literal second-point stabilizer modulo R₆ with S₆, retain its symplectic
splitting, and express the fixed-space and A₂/A₃ calculations using R₆ itself.
The equivariant map V/V₆ ≃ R₆ sends each fixed quotient to the corresponding
line. Over F₂, a point has a unique nonzero vector; this also turns the proved
vector orbit classification into the source statement on actual subspaces.

The full parabolic group and module clauses, including the irreducible chief
factors, are re-exported from `ParabolicStructure`. Middle residual quotients
are Lᵢ/(Lᵢ ∩ Rᵢ); no ambient normality or containment Rᵢ ≤ Lᵢ is inferred.

Source: Aschbacher–Smith, Lemmas 12.5.2 and 12.5.5 and the module calculations
in 12.5.7/10, printed pp.817–821/PDF pp.834–838. These are intrinsic statements
about the determinant-one action on Λ²(F₂⁵), independent of ambient fusion.
-/

@[expose] public noncomputable section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The first source point is the line of the decomposable representative. -/
theorem V₁_eq_decomposablePoint : V₁ = Submodule.span (ZMod 2) {decomposable} := by
  simp [V₁, coordinateSpan, decomposable]

/-- The orbit relation on actual exterior subspaces. -/
def InExteriorSubspaceOrbit (P Q : Submodule (ZMod 2) V) : Prop :=
  ∃ g : Group, P.map (exteriorAction 2 g) = Q

/-- Over the binary field the vector and point orbit conventions agree. -/
theorem binaryPoint_orbit_iff (v w : V) (hv : v ≠ 0) :
    InExteriorSubspaceOrbit (Submodule.span (ZMod 2) {v})
      (Submodule.span (ZMod 2) {w}) ↔ InExteriorOrbit v w := by
  constructor
  · rintro ⟨g, hg⟩
    have hmem : exteriorAction 2 g v ∈ Submodule.span (ZMod 2) {w} := by
      rw [← hg]
      exact Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_singleton v))
    rcases (mem_binaryPoint w _).mp hmem with hz | he
    · have hi := congrArg (exteriorAction 2 g⁻¹) hz
      change (exteriorAction 2 g⁻¹ * exteriorAction 2 g) v = _ at hi
      rw [← map_mul, inv_mul_cancel, map_one, map_zero] at hi
      exact (hv hi).elim
    · exact ⟨g, he⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [Submodule.map_span, Set.image_singleton, hg]⟩

/-- The two mutually exclusive orbits on the source's one-dimensional subspaces. -/
theorem exterior_point_orbits_exactly_one (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) :
    (InExteriorSubspaceOrbit V₁ P ∧ ¬ InExteriorSubspaceOrbit nondecomposablePoint P) ∨
      (InExteriorSubspaceOrbit nondecomposablePoint P ∧ ¬ InExteriorSubspaceOrbit V₁ P) := by
  have hn : P ≠ ⊥ := by
    intro h
    have := Submodule.finrank_eq_zero.mpr h
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0,
    V₁_eq_decomposablePoint, nondecomposablePoint,
    binaryPoint_orbit_iff _ _ decomposable_ne_zero,
    binaryPoint_orbit_iff _ _ nondecomposable_ne_zero]
  exact exterior_orbits_exactly_one v hv0

/-- Each involution has exactly the source natural/exterior rank pair. -/
theorem involution_displacement_ranks (g : Group) (hne : g ≠ 1) (hg : g * g = 1) :
    (Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (displacement g)) = 3) ∨
    (Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range (displacement g)) = 4) := by
  rcases involution_conjugacy_exhaustion g hne hg with h | h
  · exact Or.inl (ranks_of_isConj_j₁ h)
  · exact Or.inr (ranks_of_isConj_j₂ h)

/-- The first source involution has fixed-space codimension three. -/
theorem finrank_quotient_fixedSpace_j₁ :
    Module.finrank (ZMod 2) (V ⧸ fixedSpace j₁) = 3 := by
  have h := (fixedSpace j₁).finrank_quotient_add_finrank
  rw [finrank_fixedSpace_j₁, finrank_exteriorModule_two] at h
  omega

/-- Source R₆ is contained in the actual stabilizer of the second point. -/
theorem radicalSix_le_nondecomposableStabilizer :
    parabolicResidualTwoCore 4 ≤ nondecomposableStabilizer := by
  rw [parabolicResidualTwoCore_four]
  exact shearSubgroup_le_nondecomposableStabilizer

/-- Normality of R₆ is relative to this stabilizer. -/
instance radicalSix_normal_in_nondecomposableStabilizer :
    ((parabolicResidualTwoCore 4).subgroupOf nondecomposableStabilizer).Normal := by
  rw [parabolicResidualTwoCore_four]
  infer_instance

/-- The source stabilizer modulo its actual R₆ is the six-letter symmetric group. -/
def nondecomposableRadicalQuotientEquivSymmetricSix :
    (nondecomposableStabilizer ⧸
      (parabolicResidualTwoCore 4).subgroupOf nondecomposableStabilizer) ≃*
        Equiv.Perm (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun U : Subgroup Group => U.subgroupOf nondecomposableStabilizer)
      parabolicResidualTwoCore_four)).trans nondecomposableQuotientEquivSymmetricSix

/-- The quotient equivalence uses the actual symplectic restriction on representatives. -/
@[simp] theorem nondecomposableRadicalQuotientEquivSymmetricSix_mk
    (g : nondecomposableStabilizer) :
    nondecomposableRadicalQuotientEquivSymmetricSix (QuotientGroup.mk g) =
      nondecomposableToSymmetricSix g := rfl

/-- A splitting of the six-letter quotient by block-diagonal symplectic matrices. -/
def nondecomposableSymmetricSixSection : Equiv.Perm (Fin 6) →* nondecomposableStabilizer :=
  nondecomposableSymplecticSection.comp
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.toMonoidHom

theorem nondecomposableRadicalQuotient_section (s : Equiv.Perm (Fin 6)) :
    nondecomposableRadicalQuotientEquivSymmetricSix
      (QuotientGroup.mk (nondecomposableSymmetricSixSection s)) = s := by
  rw [nondecomposableRadicalQuotientEquivSymmetricSix_mk]
  change Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
    (nondecomposableToSymplectic (nondecomposableSymplecticSection
      (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv s))) = s
  rw [nondecomposableToSymplectic_section, MulEquiv.symm_apply_apply]

/-- R₆ also has the defining elementary-abelian structure, rather than just an order. -/
instance radicalSix_elementary : IsElementaryAbelian 2 (parabolicResidualTwoCore 4) := by
  rw [parabolicResidualTwoCore_four]
  infer_instance

/-- The source radical has order 2⁴. Its elementary structure is proved above. -/
theorem card_radicalSix : Nat.card (parabolicResidualTwoCore 4) = 16 := by
  rw [parabolicResidualTwoCore_four, card_shearSubgroup]

/-- Both source fixed and commutator spaces are the actual six-space. -/
theorem radicalSix_fixedSpace_and_commutator :
    BinaryOffender.fixedSpace (exteriorAction 2) (parabolicResidualTwoCore 4) = V₆ ∧
      BinaryOffender.subspaceCommutator (exteriorAction 2) ⊤ (parabolicResidualTwoCore 4) = V₆ := by
  rw [parabolicResidualTwoCore_four]
  exact ⟨fixedSpace_shearSubgroup, commutator_shearSubgroup⟩

/-- The quotient/radical equivalence retains the specified shear coordinates. -/
@[simp] theorem quotientSixRadicalEquiv_apply (v : V ⧸ V₆) :
    (quotientSixRadicalEquiv (Multiplicative.ofAdd v) : Group) =
      shear (shearQuotientEquiv v) := rfl

/-- The fixed quotient is precisely the line corresponding to the radical element,
under the equivariant isomorphism V/V₆ ≃ R₆, not just a dimension equality. -/
theorem fixedSpace_radicalSix_quotient (v : V ⧸ V₆) (hv : v ≠ 0) :
    (fixedSpace (quotientSixRadicalEquiv (Multiplicative.ofAdd v) : Group)).map V₆.mkQ =
      Submodule.span (ZMod 2) {v} := by
  apply Submodule.map_injective_of_injective shearQuotientEquiv.injective
  rw [quotientSixRadicalEquiv_apply,
    fixedSpace_shear_quotient _ (shearQuotientEquiv.map_ne_zero_iff.mpr hv),
    Submodule.map_span, Set.image_singleton]
  rfl

/-- Every nonidentity source radical element fixes strictly more than V₆. -/
theorem V₆_lt_fixedSpace_radicalSix (g : parabolicResidualTwoCore 4) (hg : g ≠ 1) :
    V₆ < fixedSpace g.val := by
  have hm : g.val ∈ shearSubgroup := parabolicResidualTwoCore_four ▸ g.property
  obtain ⟨u, hu⟩ := (mem_shearSubgroup g.val).mp hm
  have hn : u ≠ 0 := by
    intro hz
    apply hg
    apply Subtype.ext
    rw [← hu, hz, shear_zero]
    rfl
  rw [← hu]
  exact V₆_lt_fixedSpace_shear u hn

/-- The fixed quotients of the nonidentity radical elements are one-dimensional. -/
theorem finrank_fixedSpace_radicalSix_quotient (g : parabolicResidualTwoCore 4) (hg : g ≠ 1) :
    Module.finrank (ZMod 2) ((fixedSpace g.val).map V₆.mkQ) = 1 := by
  obtain ⟨v, rfl⟩ := quotientSixRadicalEquiv.surjective g
  have hv : v.toAdd ≠ 0 := by
    intro h
    apply hg
    change v = 1 at h
    rw [h, map_one]
  change Module.finrank (ZMod 2)
    ((fixedSpace (quotientSixRadicalEquiv (Multiplicative.ofAdd v.toAdd) : Group)).map V₆.mkQ) = 1
  rw [fixedSpace_radicalSix_quotient v.toAdd hv, finrank_span_singleton hv]

/-- The individual fixed spaces of the actual source radical span all of V. -/
theorem iSup_fixedSpace_radicalSix :
    (⨆ (g : parabolicResidualTwoCore 4) (_ : g ≠ 1), fixedSpace g.val) = ⊤ := by
  rw [parabolicResidualTwoCore_four]
  exact iSup_fixedSpace_shearSubgroup

/-- Every hyperplane of R₆ has the rank-one witness violating E.3.8 for k = 3. -/
theorem radicalSix_hyperplane_witness {A : Subgroup Group}
    (hA : A ≤ parabolicResidualTwoCore 4) (hcard : Nat.card A = 8) :
    ∃ B : Subgroup Group, B ≤ A ∧ Nat.card B = 2 ∧ B.relIndex A = 4 ∧
      BinaryOffender.fixedSpace (exteriorAction 2) A <
        BinaryOffender.fixedSpace (exteriorAction 2) B :=
  exists_line_fixedSpace_lt_of_card_eight (parabolicResidualTwoCore_four ▸ hA) hcard

/-- The pointwise centralizer of V₆ in M₆ is the actual source radical. -/
theorem pointwiseV₆_eq_radicalSix : pointwiseV₆ = parabolicResidualTwoCore 4 := by
  rw [pointwiseV₆_eq_shearSubgroup, parabolicResidualTwoCore_four]

/-- The entire source radical lies in the pointwise three-space centralizer. -/
theorem radicalSix_le_C : parabolicResidualTwoCore 4 ≤ C := by
  rw [parabolicResidualTwoCore_four]
  exact shear_le_C

instance radicalSix_normal_in_C : ((parabolicResidualTwoCore 4).subgroupOf C).Normal := by
  rw [parabolicResidualTwoCore_four]
  infer_instance

/-- The exact pointwise three-space centralizer quotient, with relative normality. -/
def centralizerRadicalQuotientEquiv :
    (C ⧸ (parabolicResidualTwoCore 4).subgroupOf C) ≃* Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun U : Subgroup Group => U.subgroupOf C)
      parabolicResidualTwoCore_four)).trans centralizerQuotientEquiv

/-- The A₃ conclusion in 12.5.7, now for R₆ = O₂(L₆T). -/
theorem flag_elementaryTwo_smallIndex_three_iff_radicalSix {A : Subgroup Group}
    (hA : A ≤ flagGroup) :
    (BinaryOffender.IsElementaryTwo A ∧ HasSmallIndexFixedSpaceProperty 3 A) ↔
      A = parabolicResidualTwoCore 4 := by
  rw [parabolicResidualTwoCore_four]
  exact flag_elementaryTwo_smallIndex_three_iff hA

/-- The intrinsic A₂ alternatives of 12.5.10 with the source radical identified. -/
theorem le_radicalSix_or_commutator_of_flag_smallIndex_two {A : Subgroup Group}
    [IsElementaryAbelian 2 A] (hA : A ≤ flagGroup)
    (hsmall : HasSmallIndexFixedSpaceProperty 2 A) :
    A ≤ parabolicResidualTwoCore 4 ∨
      V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃ A ∨
      V₁ ≤ BinaryOffender.subspaceCommutator (exteriorAction 2) V₃' A := by
  rw [parabolicResidualTwoCore_four]
  exact le_shearSubgroup_or_commutator_of_flag_smallIndex_two hA hsmall

end Representation.SL5ExteriorSquare
