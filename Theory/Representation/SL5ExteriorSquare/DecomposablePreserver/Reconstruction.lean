module
public import Theory.Representation.SL5ExteriorSquare.DecomposablePreserver.Stars

/-!
# Reconstructing SL₅(2) from a decomposable preserver

The images of the five standard stars are stars. Their pairwise intersections
force the ten exterior-basis images to be aᵢ ∧ aⱼ. The natural linear map with
columns aᵢ therefore induces the given exterior equivalence. Any nonzero vector
in its kernel would give a nonzero simple wedge killed by that equivalence,
so the natural map is invertible. Its nonzero determinant is one over F₂.

This proves the specialized preserver theorem on the literal exterior module,
using only forward preservation. The geometric input is the Grassmann clique
argument of Meierfrankenfeld–Stellmacher (1993), (1.6), pp.845–847, as developed
in `Stars`; no normalization of the exterior SL₅ image is assumed.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
namespace DecomposablePreserver

def naturalBasisVector (i : Fin 5) : N := Pi.single i 1

theorem naturalBasisVector_ne_zero (i : Fin 5) : naturalBasisVector i ≠ 0 := by
  intro h
  have hh := congrFun h i
  simp [naturalBasisVector] at hh

theorem naturalBasisVector_injective : Function.Injective naturalBasisVector := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp [naturalBasisVector, hij] at hh

theorem basis_eq_wedge (s : Fin 10) :
    basis s = wedge (naturalBasisVector (pair s 0)) (naturalBasisVector (pair s 1)) := by
  rw [basis_wedge, wedge]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem map_wedge (f : N →ₗ[ZMod 2] N) (a b : N) :
    exteriorPower.map 2 f (wedge a b) = wedge (f a) (f b) := by
  rw [wedge, exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem exists_star_images (T : V ≃ₗ[ZMod 2] V)
    (hT : ∀ v, InExteriorOrbit decomposable v → InExteriorOrbit decomposable (T v)) :
    ∃ a : Fin 5 → N, (∀ i, a i ≠ 0) ∧
      ∀ i, (star (naturalBasisVector i)).map T.toLinearMap = star (a i) := by
  have h (i : Fin 5) : ∃ a : N, a ≠ 0 ∧
      (star (naturalBasisVector i)).map T.toLinearMap = star a := by
    apply eq_star_of_totally_decomposable
    · rw [T.finrank_map_eq, finrank_star (naturalBasisVector_ne_zero i)]
    · rintro v ⟨w,hw,rfl⟩ h0
      apply hT
      apply decomposable_of_mem_star hw
      intro hw0
      exact h0 (by rw [hw0, map_zero])
  choose a ha he using h
  exact ⟨a,ha,he⟩

theorem basis_images_of_star_images (T : V ≃ₗ[ZMod 2] V)
    (a : Fin 5 → N) (ha : ∀ i, a i ≠ 0)
    (he : ∀ i, (star (naturalBasisVector i)).map T.toLinearMap = star (a i)) :
    ∀ s : Fin 10, T (basis s) = wedge (a (pair s 0)) (a (pair s 1)) := by
  have hai : Function.Injective a := by
    intro i j hij
    apply naturalBasisVector_injective
    apply star_injective (naturalBasisVector_ne_zero i) (naturalBasisVector_ne_zero j)
    apply Submodule.map_injective_of_injective T.injective
    rw [he i, he j, hij]
  intro s
  have hij : pair s 0 ≠ pair s 1 := (pairEmbedding s).injective.ne (by decide)
  have hmem : T (basis s) ∈ star (a (pair s 0)) ⊓ star (a (pair s 1)) := by
    constructor
    · rw [← he]
      refine ⟨basis s, ?_, rfl⟩
      rw [basis_eq_wedge]
      exact (mem_star _ _).mpr ⟨naturalBasisVector (pair s 1),rfl⟩
    · rw [← he]
      refine ⟨basis s, ?_, rfl⟩
      rw [basis_eq_wedge]
      exact (mem_star _ _).mpr ⟨naturalBasisVector (pair s 0),wedge_comm _ _⟩
  rw [star_intersection (ha _) (ha _) (hai.ne hij), mem_binaryPoint] at hmem
  refine hmem.resolve_left ?_
  intro hz
  exact basis.ne_zero s (T.injective (hz.trans T.map_zero.symm))

theorem injective_of_exteriorSquare_injective (f : N →ₗ[ZMod 2] N)
    (hf : Function.Injective (exteriorPower.map 2 f)) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  change x = 0
  by_contra hx0
  obtain ⟨y,hy,hxy⟩ : ∃ y : N, y ≠ 0 ∧ x ≠ y := by
    by_cases h : x = naturalBasisVector 0
    · refine ⟨naturalBasisVector 1,naturalBasisVector_ne_zero 1,?_⟩
      rw [h]
      exact naturalBasisVector_injective.ne (by decide)
    · exact ⟨naturalBasisVector 0,naturalBasisVector_ne_zero 0,h⟩
  apply wedge_ne_zero hx0 hy hxy
  apply hf
  rw [map_wedge, show f x = 0 from hx, wedge_zero_left, map_zero]

end DecomposablePreserver
open DecomposablePreserver

/-- A binary linear equivalence preserving the decomposable orbit is the
literal exterior square of a determinant-one natural matrix. -/
theorem exists_exteriorAction_of_preserves_decomposable
    (T : V ≃ₗ[ZMod 2] V)
    (hT : ∀ v, InExteriorOrbit decomposable v → InExteriorOrbit decomposable (T v)) :
    ∃ g : Group, T.toLinearMap = exteriorAction 2 g := by
  obtain ⟨a,ha,he⟩ := exists_star_images T hT
  have hb := basis_images_of_star_images T a ha he
  let M : Matrix (Fin 5) (Fin 5) (ZMod 2) := fun i j => a j i
  let f : N →ₗ[ZMod 2] N := M.mulVecLin
  have hfe (i : Fin 5) : f (naturalBasisVector i) = a i := by
    exact Matrix.mulVec_single_one M i
  have hmap : T.toLinearMap = exteriorPower.map 2 f := by
    apply basis.ext
    intro s
    change T (basis s) = exteriorPower.map 2 f (basis s)
    rw [hb, basis_eq_wedge, map_wedge, hfe, hfe]
  have hf : Function.Injective f := injective_of_exteriorSquare_injective f (by
    rw [← hmap]
    exact T.injective)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hf
  have hd0 : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have hd : M.det = 1 := (by decide : ∀ r : ZMod 2, r ≠ 0 → r = 1) _ hd0
  exact ⟨⟨M,hd⟩,hmap⟩

/-- The same statement in the literal group of units of the endomorphism ring. -/
theorem mem_exteriorAction_range_of_preserves_decomposable
    (u : (Module.End (ZMod 2) V)ˣ)
    (hu : ∀ v, InExteriorOrbit decomposable v →
      InExteriorOrbit decomposable (u.val v)) :
    u ∈ (exteriorAction 2).asGroupHom.range := by
  obtain ⟨g,hg⟩ := exists_exteriorAction_of_preserves_decomposable
    (LinearMap.GeneralLinearGroup.toLinearEquiv u) hu
  refine ⟨g,Units.ext ?_⟩
  exact hg.symm

end Representation.SL5ExteriorSquare
