module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.MovingOrthogonal
public import Theory.Representation.SL2SylowFixedRecognition.Definitions

/-! The single natural quotient supplied by G.1.6 gives the exact projection
and fixed supplement needed for the moving-cover comparison. -/

@[expose] public noncomputable section
open Representation Representation.OneCohomology
open Representation.SL2SylowFixedRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup W] [Module (ZMod 2) W]
local instance naturalProjectionFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite F] in
/-- Evaluation at the sole summand preserves the exact global-fixed kernel. -/
theorem natural_projection_of_multiplicity_one
    (ρ : Representation (ZMod 2) SL(2,F) W)
    (c : QuotientCoordinates ρ) (hc : c.multiplicity = 1) :
    ∃ p : ρ.IntertwiningMap (SL2OrthogonalCover.binaryNatural (F := F)),
      Function.Surjective p ∧ p.toLinearMap.ker = fixed ρ := by
  let i : Fin c.multiplicity := ⟨0,by omega⟩
  let p : ρ.IntertwiningMap (SL2OrthogonalCover.binaryNatural (F := F)) :=
    ((LinearMap.proj i).comp c.coordinates).intertwiningMap_of_isIntertwiningMap _ _
      (fun g w => c.intertwines g w i)
  refine ⟨p,?_,?_⟩
  · intro v
    obtain ⟨w,hw⟩ := c.surjective (fun _ => v)
    exact ⟨w,congrFun hw i⟩
  · have he : p.toLinearMap.ker = c.coordinates.ker := by
      ext w
      change c.coordinates w i = 0 ↔ c.coordinates w = 0
      constructor
      · intro hw
        funext j
        have hji : j = i := Fin.ext (by have := j.isLt; change j.val = 0; omega)
        simpa only [hji,Pi.zero_apply] using hw
      · intro hw
        exact congrFun hw i
    rw [he,c.kernel]
    ext w
    constructor
    · intro hw g
      exact hw ⟨g,Subgroup.mem_top _⟩
    · intro hw g
      exact hw g.val

omit [CharP F 2] in
/-- The G.1.6 generation hypothesis supplies the fixed supplement on the
original module; it does not assume the central extension splits. -/
theorem moving_fixed_span_of_sylow_fixed
    (ρ : Representation (ZMod 2) SL(2,F) W) (P : Sylow 2 SL(2,F))
    (h : FixedSpaceHypotheses ρ P) : Coinvariants.ker ρ ⊔ fixed ρ = ⊤ := by
  have he : BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = Coinvariants.ker ρ := by
    unfold BinaryOffender.subspaceCommutator Coinvariants.ker
    congr 1
    ext w
    constructor
    · rintro ⟨g,_,v,_,rfl⟩
      exact ⟨(g,v),rfl⟩
    · rintro ⟨⟨g,v⟩,rfl⟩
      exact ⟨g,Subgroup.mem_top _,v,Submodule.mem_top,rfl⟩
  have hf : BinaryOffender.fixedSpace ρ ⊤ = fixed ρ := by
    ext w
    exact ⟨fun hw g => hw ⟨g,Subgroup.mem_top _⟩,fun hw g => hw g.val⟩
  simpa only [he,hf] using moved_sup_fixed ρ P h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
