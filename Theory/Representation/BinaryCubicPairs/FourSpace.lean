module

public import Theory.Representation.BinaryCubicPairs.MatrixPair
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Cubic pairs on an actual four-dimensional supporting space

Choose a basis of the actual support, transport its faithful restricted
representation to matrices, and apply the checked pair theorem. Rank-nullity
supplies the fixed-space dimensions, and the literal sum of displacement
ranges supplies full support. The resulting involution acts on the original
ambient module with fixed codimension at most two.

Source application: Aschbacher--Smith E.6.24, printed p.255.
-/

public section
namespace BinaryCubicPairs
open Representation.BinaryOffender
variable {G U V : Type*} [Group G]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem exists_involution_of_four_space
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G U)
    (hσ : Function.Injective σ) (hU : Module.finrank (ZMod 2) U = 4)
    (i : U →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (haction : ∀ g u, ρ g (i u) = i (σ g u))
    (hquotient : ∀ g v, ∃ u, ρ g v - v = i u)
    (c d : G) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hc : Module.finrank (ZMod 2) (σ c - LinearMap.id).range = 2)
    (hd : Module.finrank (ZMod 2) (σ d - LinearMap.id).range = 2)
    (hfull : (σ c - LinearMap.id).range ⊔ (σ d - LinearMap.id).range = ⊤)
    (hnc : ¬ Commute c d) :
    ∃ t : G, orderOf t = 2 ∧ fixedCodim ρ (Subgroup.zpowers t) ≤ 2 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) U hU
  let e : U ≃ₗ[ZMod 2] CoordinateVector := b.equivFun
  let μ : G →* CoordinateMatrix := (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp σ
  let j : CoordinateVector →ₗ[ZMod 2] V := i.comp e.symm.toLinearMap
  have hμ : Function.Injective μ := (LinearMap.toMatrixAlgEquiv b).injective.comp hσ
  have hmat (g : G) (u : U) : (μ g).mulVec (e u) = e (σ g u) := by
    exact LinearMap.toMatrix_mulVec_repr b b (σ g) u
  have hfix (g : G) :
      Module.finrank (ZMod 2) (σ g - LinearMap.id).ker =
        Module.finrank (ZMod 2) (fixedKernel (μ g)) := by
    let p := (σ g - LinearMap.id).ker
    let q := fixedKernel (μ g)
    have heq : p.map e.toLinearMap = q := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hu' : σ g u - u = 0 := by
          simpa [p, LinearMap.sub_apply, LinearMap.id_apply] using hu
        change (μ g).mulVec (e u) - e u = 0
        rw [hmat, sub_eq_zero.mp hu', sub_self]
      · intro hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        change σ g (e.symm x) - e.symm x = 0
        apply e.injective
        rw [map_sub, map_zero, ← hmat, e.apply_symm_apply]
        exact hx
    exact (e.ofSubmodules p q heq).finrank_eq
  have hj : Function.Injective j := hi.comp e.symm.injective
  have hact : ∀ g x, ρ g (j x) = j ((μ g).mulVec x) := by
    intro g x
    change ρ g (i (e.symm x)) = i (e.symm ((μ g).mulVec x))
    rw [haction]
    apply congrArg i
    apply e.injective
    rw [e.apply_symm_apply, ← hmat, e.apply_symm_apply]
  have hquot : ∀ g v, ∃ x, ρ g v - v = j x := by
    intro g v
    obtain ⟨u, hu⟩ := hquotient g v
    refine ⟨e u, ?_⟩
    change ρ g v - v = i (e.symm (e u))
    rwa [e.symm_apply_apply]
  apply exists_involution_of_matrix_pair ρ j hj μ hμ hact hquot c d hc3 hd3
  · have hh := (σ c - LinearMap.id).finrank_range_add_finrank_ker
    rw [hc, hU, hfix c] at hh
    omega
  · have hh := (σ d - LinearMap.id).finrank_range_add_finrank_ker
    rw [hd, hU, hfix d] at hh
    omega
  · intro v
    obtain ⟨x, ⟨u, rfl⟩, y, ⟨w, rfl⟩, hxy⟩ := Submodule.mem_sup.mp
      (show e.symm v ∈ (σ c - LinearMap.id).range ⊔ (σ d - LinearMap.id).range by
        rw [hfull]; trivial)
    refine ⟨e u, e w, ?_⟩
    have hh := congrArg e hxy
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, map_add, map_sub,
      hmat, e.apply_symm_apply] using hh
  · exact hnc

end BinaryCubicPairs
