module


public import Theory.SpecificGroups.OmegaSixThree.VertexCoordinates
public import Theory.SpecificGroups.OmegaSixThree.ModelComparison
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.Generation
public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Action
import all Theory.SpecificGroups.OmegaSixThree.ModelComparison
/-!
# The marked exterior vertex embedding

The exterior square of the literal SL₄(3) action is transported to the actual
six-space coordinates and conjugated by the explicit triangle cycle. The
resulting PSp₄(3) map fixes the standard vertex, descends through the literal
center quotient, and is faithful by simplicity. Its two generator equations
match the split unitary Frobenius marking, so the construction is source-faithful
when extended by the involution.

Source: Aschbacher–Smith F.5.1(1)–F.5.3, printed pp.299–301.
-/

open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
open OmegaSixThree SixTernaryCoordinates Matrix
public noncomputable section
namespace OmegaSixThree.VertexComparison
abbrev SL := Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)
def spToSL : Sp (ZMod 3) →* SL where
  toFun g := ⟨ClassicalOrthogonal.OddFiveComparison.symplecticMatrix g,
    ClassicalOrthogonal.OddFiveComparison.symplecticMatrix_det g⟩
  map_one' := Subtype.ext ClassicalOrthogonal.OddFiveComparison.symplecticMatrix_one
  map_mul' g h := Subtype.ext (ClassicalOrthogonal.OddFiveComparison.symplecticMatrix_mul g h)
def exteriorCoordinates := Atlas.Order20160A8.Exterior.coordinates.trans Comparison.coordinates
def rawSL : SL →* LinearGroup where
  toFun g := exteriorCoordinates.symm.trans
    ((Atlas.Order20160A8.Exterior.exteriorAction g).trans exteriorCoordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change exteriorCoordinates (Atlas.Order20160A8.Bivectors.exteriorMap
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) (exteriorCoordinates.symm v)) = v
    rw [Atlas.Order20160A8.Bivectors.exteriorMap_one, LinearMap.id_apply,
      exteriorCoordinates.apply_symm_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change exteriorCoordinates (Atlas.Order20160A8.Bivectors.exteriorMap
      (g*h).val (exteriorCoordinates.symm v)) =
        exteriorCoordinates (Atlas.Order20160A8.Bivectors.exteriorMap g.val
          (exteriorCoordinates.symm (exteriorCoordinates
            (Atlas.Order20160A8.Bivectors.exteriorMap h.val (exteriorCoordinates.symm v)))))
    rw [exteriorCoordinates.symm_apply_apply, Matrix.SpecialLinearGroup.coe_mul,
      Atlas.Order20160A8.Bivectors.exteriorMap_mul, LinearMap.comp_apply]
theorem rawSL_orthogonal (g : SL) : rawSL g ∈ orthogonalGroup := by
  intro v
  change quadratic (Comparison.coordinates
    (Atlas.Order20160A8.Exterior.onD g (Comparison.coordinates.symm v))) = quadratic v
  rw [Comparison.quadratic_coordinates, Atlas.Order20160A8.Exterior.onD_form,
    ← Comparison.quadratic_coordinates, Comparison.coordinates.apply_symm_apply]
theorem rawSL_mem (g : SL) : rawSL g ∈ omegaPlusSixThree := by
  let _ := Atlas.sl_perfect (F := ZMod 3) 4 (by decide)
  let _ := Group.IsPerfect.range rawSL
  have hr : rawSL g ∈ rawSL.range := ⟨g,rfl⟩
  rw [← Subgroup.commutator_eq_self (H := rawSL.range)] at hr
  rw [Comparison.omega_eq_commutator]
  have hle : rawSL.range ≤ orthogonalGroup := by
    rintro _ ⟨a,rfl⟩
    exact rawSL_orthogonal a
  exact Subgroup.commutator_mono hle hle hr
def slToOmega : SL →* omegaPlusSixThree where
  toFun g := ⟨triangleCycle.val * rawSL g * triangleCycle.val⁻¹,
    omegaPlusSixThree.mul_mem
      (omegaPlusSixThree.mul_mem triangleCycle.property (rawSL_mem g))
      (omegaPlusSixThree.inv_mem triangleCycle.property)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; simp [map_mul, mul_assoc]
theorem slToOmega_val (g : SL) :
    (slToOmega g).val = triangleCycle.val * rawSL g * triangleCycle.val⁻¹ := by rfl
theorem rawSL_apply (g : SL) (v : Space) : rawSL g v =
    exteriorCoordinates (Atlas.Order20160A8.Bivectors.exteriorMap g.val
      (exteriorCoordinates.symm v)) := by rfl
theorem slToOmega_apply (g : SL) (v : Space) :
  (slToOmega g).val v = triangleCycle.val
    (exteriorCoordinates (Atlas.Order20160A8.Bivectors.exteriorMap g.val
      (exteriorCoordinates.symm (triangleCycle.val.symm v)))) := by
  rw [slToOmega_val, LinearEquiv.mul_apply, LinearEquiv.mul_apply, rawSL_apply]
  simp only [LinearEquiv.coe_inv]
theorem generator_fixes_vector (i : Fin 2) :
    (slToOmega (spToSL (symplecticGenerator i))).val (e 5) = e 5 := by
  rw [slToOmega_apply]
  revert i
  decide +kernel

def spToOmega : Sp (ZMod 3) →* omegaPlusSixThree := slToOmega.comp spToSL

theorem spToOmega_fixes_vector (g : Sp (ZMod 3)) : (spToOmega g).val (e 5) = e 5 := by
  let K := (MulAction.stabilizer LinearGroup (e 5)).comap
    (omegaPlusSixThree.subtype.comp spToOmega)
  have hle : Subgroup.closure (Set.range symplecticGenerator) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact generator_fixes_vector i
  rw [symplectic_generators_generate] at hle
  exact hle (Subgroup.mem_top g)

theorem spToSL_negIdentity_val :
    (spToSL (negIdentity (ZMod 3))).val = -1 := by
  have he : (negIdentity (ZMod 3)).val =
      -(1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) := by
    apply Matrix.ext
    intro i j
    have h := congrFun (negIdentity_smul (F := ZMod 3) (Pi.single j 1)) i
    change ((negIdentity (ZMod 3)).val *ᵥ Pi.single j 1) i = _ at h
    simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply] using h
  change Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) finSumFinEquiv
    (negIdentity (ZMod 3)).val = -1
  rw [he, map_neg, map_one]

theorem spToOmega_negIdentity : spToOmega (negIdentity (ZMod 3)) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
  intro i
  simp only [LinearEquiv.coe_coe, Pi.basisFun_apply, Subgroup.coe_one,
    LinearEquiv.coe_one, id_eq]
  rw [spToOmega, MonoidHom.comp_apply, slToOmega_apply, spToSL_negIdentity_val]
  revert i
  decide +kernel

def pspToOmega : PSp (ZMod 3) →* omegaPlusSixThree :=
  QuotientGroup.lift _ spToOmega (by
    intro g hg
    rcases (mem_center_iff g).mp hg with rfl | rfl
    · exact map_one spToOmega
    · exact spToOmega_negIdentity)

theorem pspToOmega_projection (g : Sp (ZMod 3)) :
    pspToOmega (QuotientGroup.mk g) = spToOmega g := by rfl

theorem pspToOmega_fixes_vector (g : PSp (ZMod 3)) : (pspToOmega g).val (e 5) = e 5 := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp (ZMod 3))) g
  exact spToOmega_fixes_vector g

theorem pspToOmega_generator_zero_ne_one : pspToOmega (projectiveGenerator 0) ≠ 1 := by
  intro h
  have hi (i : Fin 6) := congrArg (fun g : omegaPlusSixThree => g.val (e i)) h
  have htest : ¬ ∀ i : Fin 6, triangleCycle.val
      (exteriorCoordinates (Atlas.Order20160A8.Bivectors.exteriorMap
        (spToSL (symplecticGenerator 0)).val
        (exteriorCoordinates.symm (triangleCycle.val.symm (e i))))) = e i := by
    decide +kernel
  apply htest
  intro i
  have hi := hi i
  change (slToOmega (spToSL (symplecticGenerator 0))).val (e i) = e i at hi
  rwa [slToOmega_apply] at hi

theorem pspToOmega_injective : Function.Injective pspToOmega := by
  let _ := projective_simple (F := ZMod 3) (by norm_num)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : pspToOmega.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply pspToOmega_generator_zero_ne_one
    change projectiveGenerator 0 ∈ pspToOmega.ker
    rw [h]
    exact Subgroup.mem_top _


theorem pspToOmega_generator (i : Fin 2) :
    pspToOmega (projectiveGenerator i) = slToOmega (spToSL (symplecticGenerator i)) := by rfl

theorem graphInvolution_inv : vertexGraphInvolution⁻¹ = vertexGraphInvolution := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  exact graphInvolution_sq

theorem pspToOmega_conjugates_generator_zero :
    vertexGraphInvolution * pspToOmega (projectiveGenerator 0) * vertexGraphInvolution⁻¹ =
      (pspToOmega (projectiveGenerator 0))⁻¹ := by
  rw [pspToOmega_generator, graphInvolution_inv]
  apply eq_inv_iff_mul_eq_one.mpr
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
  intro i
  simp only [LinearEquiv.coe_coe, Pi.basisFun_apply, Subgroup.coe_mul, Subgroup.coe_one,
    LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, slToOmega_apply]
  revert i
  decide +kernel

theorem pspToOmega_conjugates_generator_one :
    vertexGraphInvolution * pspToOmega (projectiveGenerator 1) * vertexGraphInvolution⁻¹ =
      pspToOmega (projectiveGenerator 1) := by
  have hc : vertexGraphInvolution * pspToOmega (projectiveGenerator 1) =
      pspToOmega (projectiveGenerator 1) * vertexGraphInvolution := by
    rw [pspToOmega_generator]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
    intro i
    simp only [LinearEquiv.coe_coe, Pi.basisFun_apply, Subgroup.coe_mul,
      LinearEquiv.mul_apply, slToOmega_apply]
    revert i
    decide +kernel
  rw [hc, mul_inv_cancel_right]

end OmegaSixThree.VertexComparison
