module
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Irreducibility of a natural conjugation action

The natural action of SL₂(F) is transitive on nonzero vectors. Thus any
nontrivial subgroup invariant under a surjective conjugation action is
the whole natural module, including when the underlying scalars are F₂.
This form preserves the original ambient subgroups and conjugation map.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Representation
variable {G F : Type*} [Group G] [Field F] [Algebra (ZMod 2) F]

/-- A natural SL2 conjugation module has no proper nonzero invariant subgroup. -/
theorem natural_conjugation_minimal
    (H A : Subgroup G) [IsElementaryAbelian 2 A]
    (q : H →* SL(2,F)) (hq : Function.Surjective q)
    (ρ : Representation (ZMod 2) SL(2,F) (Additive A))
    (hc : ∀ (l : H) (z : Additive A),
      ((ρ (q l) z).toMul : G) = (l : G)*z.toMul*(l : G)⁻¹)
    (E : Additive A ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z))
    (D : Subgroup G) (hDA : D ≤ A) (hHD : H ≤ normalizer (D : Set G)) :
    D = ⊥ ∨ D = A := by
  by_cases hzero : D = ⊥
  · exact Or.inl hzero
  right
  obtain ⟨x,hx,hxne⟩ := D.bot_or_exists_ne_one.resolve_left hzero
  let v : Additive A := Additive.ofMul ⟨x,hDA hx⟩
  have hv : E v ≠ 0 := by
    intro he
    have hh : v = 0 := E.injective (he.trans E.map_zero.symm)
    exact hxne (congrArg (fun z : Additive A => (z.toMul : G)) hh)
  apply le_antisymm hDA
  intro z hz
  by_cases hz1 : z = 1
  · exact hz1 ▸ D.one_mem
  let w : Additive A := Additive.ofMul ⟨z,hz⟩
  have hw : E w ≠ 0 := by
    intro he
    have hh : w = 0 := E.injective (he.trans E.map_zero.symm)
    exact hz1 (congrArg (fun z : Additive A => (z.toMul : G)) hh)
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F (E v) (E w) hv hw
  obtain ⟨l,rfl⟩ := hq g
  have hmove : ρ (q l) v = w := E.injective ((hE _ _).trans hg)
  have hconj : (l : G)*x*(l : G)⁻¹ = z :=
    (hc l v).symm.trans (congrArg (fun z : Additive A => (z.toMul : G)) hmove)
  exact hconj ▸ (mem_normalizer_iff.mp (hHD l.property) x).mp hx
end Representation
