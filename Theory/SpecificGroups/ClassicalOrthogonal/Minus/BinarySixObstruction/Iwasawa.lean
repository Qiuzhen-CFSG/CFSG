module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.ThreeRank

/-!
# Iwasawa assembly for the binary six-dimensional minus group

The Siegel subgroups at singular points are abelian and are permuted by
conjugation in the actual orthogonal commutator group. If Siegel transformations
generate that group, they give an Iwasawa structure. The action is faithful by
the explicit spanning calculation in `Basic`. Hence primitivity and perfectness
complete the simplicity argument, and the characteristic-two scalar-quotient
isomorphism transfers it to the required projective group.

The final theorem retains the three outstanding structural hypotheses explicitly;
it does not assert unconditional simplicity. These are the geometric and
algebraic inputs to the classical-group argument for GLS3 §2.7, used for the
section in Table 5.3o and Aschbacher--Smith A.2.19.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace ClassicalOrthogonal.Minus.BinarySixObstruction

/-- The defining action viewed as an isometry of the full quadratic form. -/
def asIsometry (g : OmegaGroup) : naturalForm.IsometryEquiv naturalForm where
  toLinearEquiv := g.val.val
  map_app' := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup naturalForm _).mp g.val.prop

theorem conjugate_mem_rootSubgroup (g : OmegaGroup) (p : Point)
    (u : OmegaGroup) (hu : u ∈ rootSubgroup p) :
    g * u * g⁻¹ ∈ rootSubgroup (g • p) := by
  obtain ⟨v, hv⟩ := hu
  let w : RootParameter (g • p) := ⟨g.val.val v.toAdd.val, by
    change naturalForm.polarBilin (asIsometry g p.val) (asIsometry g v.toAdd.val) = 0
    rw [Quadratic.isometry_polar]
    exact v.toAdd.prop⟩
  refine ⟨Multiplicative.ofAdd w, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hvx := congrArg (fun h : FullGroup => h.val (g.val.val.symm x)) hv
  change Quadratic.siegel naturalForm p.val v.toAdd.val (g.val.val.symm x) =
    u.val.val (g.val.val.symm x) at hvx
  change Quadratic.siegel naturalForm (g.val.val p.val) (g.val.val v.toAdd.val) x =
    g.val.val (u.val.val (g.val.val.symm x))
  rw [← hvx]
  have hc := Quadratic.siegel_covariant naturalForm (asIsometry g) p.val v.toAdd.val
    (g.val.val.symm x)
  change g.val.val (Quadratic.siegel naturalForm p.val v.toAdd.val (g.val.val.symm x)) =
    Quadratic.siegel naturalForm (g.val.val p.val) (g.val.val v.toAdd.val)
      (g.val.val (g.val.val.symm x)) at hc
  simpa only [LinearEquiv.apply_symm_apply] using hc.symm

theorem rootSubgroup_conjugate (g : OmegaGroup) (p : Point) :
    rootSubgroup (g • p) = MulAut.conj g • rootSubgroup p := by
  apply le_antisymm
  · intro u hu
    refine ⟨g⁻¹ * u * g, ?_, ?_⟩
    · simpa using conjugate_mem_rootSubgroup g⁻¹ (g • p) u hu
    · change g * (g⁻¹ * u * g) * g⁻¹ = u
      group
  · rintro _ ⟨u, hu, rfl⟩
    exact conjugate_mem_rootSubgroup g p u hu

/-- Equality of the elementary and commutator subgroups makes the root family generate. -/
theorem rootSubgroup_generates
    (hgen : elementarySubgroup naturalForm = commutator FullGroup) :
    (⨆ p : Point, rootSubgroup p) = ⊤ := by
  apply top_unique
  intro g _
  have hg : g.val ∈ elementarySubgroup naturalForm := hgen.symm ▸ g.prop
  let S : Subgroup OmegaGroup := ⨆ p : Point, rootSubgroup p
  have hle : elementarySubgroup naturalForm ≤ S.map (commutator FullGroup).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro u ⟨v, w, hv, hvw, rfl⟩
    by_cases hv0 : v = 0
    · have he : siegelElement naturalForm v w hv hvw = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        simp [siegelElement, Quadratic.siegelIsometry, Quadratic.siegel, hv0]
      rw [he]
      exact (S.map (commutator FullGroup).subtype).one_mem
    · have hu : siegelElement naturalForm v w hv hvw ∈ commutator FullGroup :=
        hgen ▸ siegelElement_mem naturalForm v w hv hvw
      let u : OmegaGroup := ⟨siegelElement naturalForm v w hv hvw, hu⟩
      refine ⟨u, ?_, rfl⟩
      apply le_iSup (rootSubgroup) (⟨v, hv0, hv⟩ : Point)
      exact ⟨Multiplicative.ofAdd (⟨w, hvw⟩ : RootParameter ⟨v, hv0, hv⟩), rfl⟩
  obtain ⟨u, hu, he⟩ := hle hg
  have : u = g := Subtype.ext he
  exact this ▸ hu

/-- The root groups supply Iwasawa data once elementary generation is known. -/
def iwasawaStructure
    (hgen : elementarySubgroup naturalForm = commutator FullGroup) :
    MulAction.IwasawaStructure OmegaGroup Point where
  T := rootSubgroup
  is_comm := rootSubgroup_commutative
  is_conj := rootSubgroup_conjugate
  is_generator := rootSubgroup_generates hgen

instance omega_nontrivial : Nontrivial OmegaGroup :=
  Function.Injective.nontrivial embedding_injective

/-- Assembly on the actual commutator group followed by its literal scalar quotient. -/
theorem isSimpleGroup_of_geometry_and_generation
    [MulAction.IsPreprimitive OmegaGroup Point]
    (hgen : elementarySubgroup naturalForm = commutator FullGroup)
    (hperfect : commutator OmegaGroup = ⊤) :
    IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) := by
  let : IsSimpleGroup OmegaGroup :=
    (iwasawaStructure hgen).isSimpleGroup hperfect inferInstance
  exact (minusProjectiveEquiv (F := F) 3).symm.isSimpleGroup

end ClassicalOrthogonal.Minus.BinarySixObstruction
