module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Characters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.RootWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.Conjugation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
# Generation for arbitrary F4 root models

The concrete Chevalley root curves generate the literal closed F4 carrier.
For any torus conjugate to the concrete split torus, uniqueness of each
concrete root weight identifies every conjugated root curve among the roots
of an arbitrary realization. Taking the inverse image of the generated
subgroup under conjugation proves generation by the realization's roots.
Neither its indexing nor its chosen base is compared to the standard base.

The final theorem discharges both geometric inputs using concrete torus
maximality, maximal-torus conjugacy and root-weight uniqueness in
characteristic two. Over the algebraic closure of a finite field it proves
the whole-group generation clause for every supplied semisimple F4 model.
The earlier conditional reductions retain their interfaces. The proof uses
neither coroot generation, character separation, root-lattice equality, nor
universality.

Source: GLS3, Theorem 1.9.5(b),(c),(i), `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

universe u

namespace Theory.AlgebraicGroup.RootGroupData
open ReeF4.BinaryDegree.ExceptionalTensor
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The literal F4 root generators transfer to any realized root datum after
torus conjugacy and uniqueness at the concrete root weights are supplied. -/
theorem f4_generated_eq_top_of_torus_conjugacy_and_unique_weights
    {T : ClosedSubgroup (F4Chevalley.Carrier (k := F))}
    (D : RootGroupData (F4Chevalley.Carrier (k := F)) T) (hD : D.IsRealization)
    (g : Variety.Point (F4Chevalley.Carrier (k := F)))
    (hT : T = (F4Chevalley.splitTorus (k := F)).conjugate g)
    (hunique : ∀ (r : F4Chevalley.Root) (Y : ClosedSubgroup (F4Chevalley.Carrier (k := F))),
      IsTorusRootSubgroup F4Chevalley.splitTorus Y →
      RootWeightEquation F4Chevalley.splitTorus Y (F4Chevalley.rootWeight r) →
      Y = F4Chevalley.rootSubgroup r) :
    RootSubgroupGenerated D Set.univ = ⊤ := by
  subst T
  let H := RootSubgroupGenerated D Set.univ
  let c := MulAut.conj g
  have hle : Subgroup.closure
      (Set.range (fun rt : F4Chevalley.Root × F => algebraicRootElement rt.1 rt.2)) ≤
        H.comap c.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨r, t⟩, rfl⟩
    obtain ⟨α, hα⟩ := D.exists_rootSubgroup_eq_conjugate_of_unique_weight g hD
      (F4Chevalley.rootSubgroup_package r).1 (F4Chevalley.rootSubgroup_package r).2
      (hunique r)
    change c (algebraicRootElement r t) ∈ H
    apply rootSubgroup_le_RootSubgroupGenerated D (Set.mem_univ α)
    change c (algebraicRootElement r t) ∈ D.rootSubgroup α
    rw [hα, ClosedSubgroup.mem_conjugate_iff]
    change g⁻¹ * (g * algebraicRootElement r t * g⁻¹) * g ∈ _
    rw [show g⁻¹ * (g * algebraicRootElement r t * g⁻¹) * g =
      algebraicRootElement r t by group]
    exact ⟨kPlusPoint t, rfl⟩
  rw [algebraicRootElements_generate] at hle
  apply top_unique
  intro x _
  have hx := hle (Subgroup.mem_top (c.symm x))
  change c (c.symm x) ∈ H at hx
  simpa only [MulEquiv.apply_symm_apply] using hx

end Theory.AlgebraicGroup.RootGroupData

namespace Theory.AlgebraicGroup.RootSystemModel

variable {F : Type u} [Field F] [IsAlgClosed F]

/-- Torus conjugacy and the concrete root-weight uniqueness theorem suffice for
GLS3 1.9.5(i) on any actual F4 model, with any chosen base. -/
theorem f4_rootGeneration_of_torus_conjugacy_and_unique_weights
    (M : RootSystemModel StandardRootSystem.typeF4RootPairingULift
      (F4Chevalley.Carrier (k := F)))
    (hconj : ∃ g : Variety.Point (F4Chevalley.Carrier (k := F)),
      M.torus = (F4Chevalley.splitTorus (k := F)).conjugate g)
    (hunique : ∀ (r : F4Chevalley.Root) (Y : ClosedSubgroup (F4Chevalley.Carrier (k := F))),
      IsTorusRootSubgroup F4Chevalley.splitTorus Y →
      RootWeightEquation F4Chevalley.splitTorus Y (F4Chevalley.rootWeight r) →
      Y = F4Chevalley.rootSubgroup r) :
    RootSubgroupGenerated M.rootData Set.univ ⊔ M.torus.toSubgroup = ⊤ := by
  obtain ⟨g, hg⟩ := hconj
  rw [M.rootData.f4_generated_eq_top_of_torus_conjugacy_and_unique_weights
    M.realization g hg hunique, top_sup_eq]

/-- GLS3 1.9.5(i), applied to the whole semisimple F4 carrier over the
algebraic closure of a finite characteristic-two field. The torus and the
chosen base belong to the supplied model and need not be the standard ones.
Concrete maximality, torus conjugacy and root-weight uniqueness discharge
all geometric premises of the generation reduction. -/
theorem f4_rootGeneration
    {E : Type u} [Field E] [Finite E] [CharP E 2]
    (M : RootSystemModel StandardRootSystem.typeF4RootPairingULift
      (F4Chevalley.Carrier (k := AlgebraicClosure E)))
    (hsemi : IsSemisimpleAlgebraicGroup
      (F4Chevalley.Carrier (k := AlgebraicClosure E))) :
    RootSubgroupGenerated M.rootData Set.univ ⊔ M.torus.toSubgroup = ⊤ :=
  M.f4_rootGeneration_of_torus_conjugacy_and_unique_weights
    (F4Chevalley.TorusConjugacy.model_torus_conjugate M)
    (F4Chevalley.concreteRootSubgroup_eq_of_semisimple_maximalTorus hsemi
      F4Chevalley.TorusConjugacy.splitTorus_isMaximal)

end Theory.AlgebraicGroup.RootSystemModel
