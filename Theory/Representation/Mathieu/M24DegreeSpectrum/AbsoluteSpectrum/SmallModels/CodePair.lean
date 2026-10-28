module

public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.ScalarDescent

/-!
# The two native eleven-dimensional modules over characteristic two

The same pointwise octad kernel has at most four fixed dimensions on the
code and at least six on the cocode. This distinguishes the binary modules.
Descent of representation equivalences preserves this distinction under
arbitrary scalar extension. Absolute irreducibility of the native actions
then gives two irreducible modules, transported to eleven coordinates.

Sources: Aschbacher--Smith, H.13.1--2, H.15.2 and H.16.2;
James, The modular characters of the Mathieu groups, J. Algebra 27 (1973),
57--111. This supplies the degree-eleven candidates used in GM02,
Proposition 5.1, manuscript p.17, on the actual Witt-design M24 carrier.
-/

public section
noncomputable section
open scoped TensorProduct Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
open MathieuCode MathieuCode.SmallKernelFixed

private theorem code_kernel_fixed_le_four :
    Module.finrank (ZMod 2)
      (fixedSpace codeRepresentation (octadPointwiseKernel seedOctad)) ≤ 4 := by
  have hle := Submodule.finrank_mono (le_inf
    (fixedSpace_antitone golayRepresentation
      (Subgroup.zpowers_le.mpr (translation_mem 1)))
    (fixedSpace_antitone golayRepresentation
      (Subgroup.zpowers_le.mpr (translation_mem 2))))
  rw [golay_pair_finrank 1 2 (by decide) (by decide) (by decide)] at hle
  have hlift := finrank_fixedSpace_golay (octadPointwiseKernel seedOctad)
    (24 : Fin 24) (fun g hg => (mem_octadPointwiseKernel _ _).mp hg _
      ((mem_seedOctad _).mpr (Or.inl rfl)))
  omega

private theorem cocode_kernel_fixed_ge_six :
    6 ≤ Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation (octadPointwiseKernel seedOctad)) := by
  have hle : supportedPairSpace seedOctad.val ≤
      fixedSpace cocodeRepresentation (octadPointwiseKernel seedOctad) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨P, hP, rfl⟩ g
    apply (pairVector_fixed_iff g.val P).mpr
    rw [Finset.smul_finset_def]
    calc
      _ = P.val.image id := Finset.image_congr fun i hi =>
        (mem_octadPointwiseKernel _ _).mp g.property i (hP hi)
      _ = P.val := Finset.image_id
  simpa only [CocodeOctad.finrank_supportedPairSpace] using Submodule.finrank_mono hle

/-- The actual binary code and cocode are inequivalent as marked M24 modules. -/
theorem code_cocode_inequivalent : IsEmpty (codeRepresentation.Equiv cocodeRepresentation) := by
  constructor
  intro e
  have hmap := fixedSpace_map_equivariant codeRepresentation cocodeRepresentation
    (MonoidHom.id M24) e.toLinearEquiv
    (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v)
    (octadPointwiseKernel seedOctad)
  simp only [Subgroup.map_id] at hmap
  have he := e.toLinearEquiv.finrank_map_eq
    (fixedSpace codeRepresentation (octadPointwiseKernel seedOctad))
  rw [hmap] at he
  have := code_kernel_fixed_le_four
  have := cocode_kernel_fixed_ge_six
  omega

variable (F : Type*) [Field F] [CharP F 2]

attribute [local instance] ZMod.algebra

/-- Inequivalence survives genuine scalar extension to any characteristic-two field. -/
theorem extended_code_cocode_inequivalent :
    IsEmpty ((extendScalars F codeRepresentation).Equiv
      (extendScalars F cocodeRepresentation)) := by
  constructor
  intro e
  obtain ⟨d⟩ := repEquiv_of_extendScalars codeRepresentation cocodeRepresentation
    ⟨RepEquiv.ofRepresentationEquiv e⟩
  exact code_cocode_inequivalent.false d.toRepresentationEquiv

private def codeCoordinates : (F ⊗[ZMod 2] Code) ≃ₗ[F] (Fin 11 → F) :=
  (Module.finBasisOfFinrankEq F (F ⊗[ZMod 2] Code)
    (by rw [Module.finrank_baseChange, finrank_code])).equivFun

private def cocodeCoordinates : (F ⊗[ZMod 2] Cocode) ≃ₗ[F] (Fin 11 → F) :=
  (Module.finBasisOfFinrankEq F (F ⊗[ZMod 2] Cocode)
    (by rw [Module.finrank_baseChange, finrank_cocode])).equivFun

/-- The native code, extended to F and transported to eleven coordinates. -/
def code : Representation F M24 (Fin 11 → F) :=
  (codeCoordinates F).conjRingEquiv.toMonoidHom.comp (extendScalars F codeRepresentation)

/-- The native cocode, extended to F and transported to eleven coordinates. -/
def cocode : Representation F M24 (Fin 11 → F) :=
  (cocodeCoordinates F).conjRingEquiv.toMonoidHom.comp (extendScalars F cocodeRepresentation)

/-- The coordinate code keeps the native group marking. -/
def codeEquiv : (extendScalars F codeRepresentation).Equiv (code F) :=
  .mk (codeCoordinates F) (by
    intro g
    apply LinearMap.ext
    intro v
    change codeCoordinates F ((extendScalars F codeRepresentation) g v) =
      codeCoordinates F ((extendScalars F codeRepresentation) g
        ((codeCoordinates F).symm (codeCoordinates F v)))
    rw [LinearEquiv.symm_apply_apply])

/-- The coordinate cocode keeps the native group marking. -/
def cocodeEquiv : (extendScalars F cocodeRepresentation).Equiv (cocode F) :=
  .mk (cocodeCoordinates F) (by
    intro g
    apply LinearMap.ext
    intro v
    change cocodeCoordinates F ((extendScalars F cocodeRepresentation) g v) =
      cocodeCoordinates F ((extendScalars F cocodeRepresentation) g
        ((cocodeCoordinates F).symm (cocodeCoordinates F v)))
    rw [LinearEquiv.symm_apply_apply])

theorem code_irreducible : IsIrreducible (code F) := by
  let : codeRepresentation.IsAbsolutelyIrreducible := code_isAbsolutelyIrreducible
  exact (RepEquiv.ofRepresentationEquiv (codeEquiv F)).irreducible_euqiv.mp
    (IsAbsolutelyIrreducible.irreducible_of_extension codeRepresentation F)

theorem cocode_irreducible : IsIrreducible (cocode F) := by
  let : cocodeRepresentation.IsAbsolutelyIrreducible := cocode_isAbsolutelyIrreducible
  exact (RepEquiv.ofRepresentationEquiv (cocodeEquiv F)).irreducible_euqiv.mp
    (IsAbsolutelyIrreducible.irreducible_of_extension cocodeRepresentation F)

/-- The two coordinate actions remain inequivalent over every characteristic-two field. -/
theorem code_cocode_coordinates_inequivalent : IsEmpty ((code F).Equiv (cocode F)) := by
  constructor
  intro e
  exact (extended_code_cocode_inequivalent F).false
    (((codeEquiv F).trans e).trans (cocodeEquiv F).symm)

/-- Two actual inequivalent simple eleven-dimensional M24 modules. -/
theorem elevenModelsExist :
    ∃ ρ : Fin 2 → Representation F M24 (Fin 11 → F),
      (∀ i, IsIrreducible (ρ i)) ∧
      Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)) := by
  refine ⟨![code F, cocode F], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact code_irreducible F
    · exact cocode_irreducible F
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact code_cocode_coordinates_inequivalent F
    · exact ⟨fun e => (code_cocode_coordinates_inequivalent F).false e.symm⟩
    · exact (hij rfl).elim

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
