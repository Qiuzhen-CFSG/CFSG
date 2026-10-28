module
public import Theory.Representation.SymplecticFourOrthogonalCover.InvariantRefinement
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Conjugates
public import Theory.Representation.BinaryOffender.SubspaceAction


/-!
# Fixed vectors in dual symplectic covers

A fixed vector outside the natural submodule separates from that submodule
by a linear functional. On the dual central cover, the functional lies in
the kernel but outside the actor's commutator space. The existing orthogonal
cover theorem then supplies an invariant quadratic refinement. Consequently
an actor with no invariant refinement fixes only vectors in the natural image.

Source: MS93 (1.5)(ii) and its dual-module application in (3.4), printed p.869.
-/

public noncomputable section
open Representation Representation.OneCohomology Representation.BinaryOffender
namespace Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
variable {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}

/-- A fixed vector outside the natural submodule in a dual cover forces the
actor to preserve a quadratic refinement of the original symplectic form. -/
theorem dualCover_refinement_of_fixed_escape
    (i : (binaryNatural (K := F)).IntertwiningMap σ)
    (hi : Function.Injective i) (hdual : IsDualCover i.range)
    (A : Subgroup (L (K := F))) (w : W)
    (hw : w ∈ fixed (σ.comp A.subtype)) (he : w ∉ i.toLinearMap.range) :
    ∃ c : Natural (K := F), ∀ a : A, ∀ v,
      refinement c (binaryNatural a.val v) = refinement c v := by
  let p₀ := dualIntertwining i
  have hp₀ := dualCover_dual_isCover i hi hdual
  let e := binarySelfDual (K := F)
  let p : σ.dual.IntertwiningMap (binaryNatural (K := F)) :=
    (e.symm.toLinearMap.comp p₀.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g f
      apply e.injective
      change e (e.symm (p₀ (σ.dual g f))) = e (binaryNatural g (e.symm (p₀ f)))
      rw [e.apply_symm_apply,p₀.isIntertwining,binarySelfDual_equivariant,
        e.apply_symm_apply])
  have hp : IsCover p := by
    refine ⟨e.symm.surjective.comp hp₀.1,?_,hp₀.2.2⟩
    intro f hf
    apply hp₀.2.1
    change e.symm (p₀ f) = 0 at hf
    exact e.symm.injective (hf.trans (map_zero e.symm).symm)
  apply cover_preserves_refinement_of_kernel_escape p hp A
  intro hker
  obtain ⟨f,hfw,hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem he inferInstance
  have hfp : f ∈ p.toLinearMap.ker := by
    change e.symm (p₀ f) = 0
    rw [LinearEquiv.map_eq_zero_iff]
    apply LinearMap.ext
    intro v
    change f (i v) = 0
    have hz : f (i v) ∈ (⊥ : Submodule (ZMod 2) (ZMod 2)) := by
      rw [←hf]
      exact Submodule.mem_map_of_mem ⟨v,rfl⟩
    exact hz
  have hzero : Coinvariants.ker (σ.dual.comp A.subtype) ≤
      LinearMap.ker (Module.Dual.eval (ZMod 2) W w) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,l⟩,rfl⟩
    change l (σ g.val⁻¹ w) - l w = 0
    rw [show σ g.val⁻¹ w = w from hw g⁻¹,sub_self]
  exact hfw (hzero (hker hfp))

/-- The contrapositive form used for the second source star bound. -/
theorem dualCover_fixed_le_natural_of_no_refinement
    (i : (binaryNatural (K := F)).IntertwiningMap σ)
    (hi : Function.Injective i) (hdual : IsDualCover i.range)
    (A : Subgroup (L (K := F)))
    (hn : ¬ ∃ c : Natural (K := F), ∀ a : A, ∀ v,
      refinement c (binaryNatural a.val v) = refinement c v) :
    fixed (σ.comp A.subtype) ≤ i.toLinearMap.range := by
  intro w hw
  by_contra he
  exact hn (dualCover_refinement_of_fixed_escape i hi hdual A w hw he)

end Representation.SymplecticFourOrthogonalCover
