module
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Orders
import all Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Orders

/-!
# Hyperplane stabilizers in a binary three-space

The restriction to the hyperplane has image GL₂(2) and kernel of order
four, so the stabilizer has order 24 and index seven. Its natural fixed
space is zero: a fixed nonzero vector would span an invariant line, whereas
a parabolic has only its defining subspace as a proper nonzero invariant
subspace.

This is the local quotient used by the Mathieu source edge-rigidity proof,
Aschbacher, *Sporadic Groups* (1994), 41.4, p.222. The internal import reuses
the generic restriction map and its surjectivity from the existing order
proof, without exposing that implementation or rebuilding its owner.
-/

public noncomputable section
open Subgroup Module
namespace BinaryLinear.FourParabolicAction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The natural binary three-space group has order 168. -/
theorem card_GL_three (hV : finrank (ZMod 2) V = 3) : Nat.card (V ≃ₗ[ZMod 2] V) = 168 := by
  let b : Basis (Fin 3) (ZMod 2) V := (finBasis (ZMod 2) V).reindex (finCongr hV)
  let e := (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- A binary three-space hyperplane stabilizer has order 24. -/
theorem threeSpace_hyperplane_card (W : Submodule (ZMod 2) V)
    (hV : finrank (ZMod 2) V = 3) (hW : finrank (ZMod 2) W = 2) :
    Nat.card (parabolic W) = 24 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hi := BinaryFourFixedSpace.index_pointwiseFixer W
  rw [hV, hW] at hi
  norm_num [Fin.prod_univ_succ] at hi
  have hfix : Nat.card (BinaryFourFixedSpace.pointwiseFixer W) = 4 := by
    have hc := (BinaryFourFixedSpace.pointwiseFixer W).card_mul_index
    rw [card_GL_three hV, hi] at hc
    omega
  have hGL : Nat.card (W ≃ₗ[ZMod 2] W) = 6 := by
    let b : Basis (Fin 2) (ZMod 2) W := (finBasis (ZMod 2) W).reindex (finCongr hW)
    let e := (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
    rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hk : (restriction W).ker =
      (BinaryFourFixedSpace.pointwiseFixer W).subgroupOf (parabolic W) := by
    ext g
    change restriction W g = 1 ↔ ∀ w ∈ W, g.val w = w
    constructor
    · intro h w hw
      exact congrArg Subtype.val (LinearEquiv.congr_fun h ⟨w, hw⟩)
    · intro h
      ext w
      exact h w w.property
  have hle : BinaryFourFixedSpace.pointwiseFixer W ≤ parabolic W := by
    intro g hg v
    constructor
    · intro hv
      exact g.injective (hg (g v) hv) ▸ hv
    · intro hv
      rw [hg v hv]
      exact hv
  have hc := (restriction W).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (restriction_surjective W),
    card_top, hGL, hk, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hfix] at hc
  omega

/-- A binary three-space hyperplane stabilizer has odd index seven. -/
theorem threeSpace_hyperplane_index (W : Submodule (ZMod 2) V)
    (hV : finrank (ZMod 2) V = 3) (hW : finrank (ZMod 2) W = 2) :
    (parabolic W).index = 7 := by
  have hc := (parabolic W).card_mul_index
  rw [threeSpace_hyperplane_card W hV hW, card_GL_three hV] at hc
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- The natural action of a hyperplane stabilizer in binary dimension three
has no nonzero fixed vector. -/
theorem threeSpace_hyperplane_fixed (W : Submodule (ZMod 2) V)
    (hV : finrank (ZMod 2) V = 3) (hW : finrank (ZMod 2) W = 2)
    (v : V) (hv : ∀ g ∈ parabolic W, g v = v) : v = 0 := by
  by_contra hn
  let U := Submodule.span (ZMod 2) {v}
  have hd : finrank (ZMod 2) U = 1 := finrank_span_singleton hn
  have hU0 : U ≠ ⊥ := by intro he; rw [he, finrank_bot] at hd; contradiction
  have hU1 : U ≠ ⊤ := by intro he; rw [he, finrank_top, hV] at hd; contradiction
  have hle : parabolic W ≤ parabolic U := by
    intro g hg x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
      apply Submodule.mem_span_singleton.mpr
      refine ⟨a, g.injective ?_⟩
      rw [map_smul, hv g hg]
      exact ha
    · intro hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hv g hg]
      exact Submodule.smul_mem U a (Submodule.subset_span (Set.mem_singleton v))
  have he := parabolic_le_imp_eq hU0 hU1 hle
  rw [← he, hW] at hd
  contradiction

end BinaryLinear.FourParabolicAction
