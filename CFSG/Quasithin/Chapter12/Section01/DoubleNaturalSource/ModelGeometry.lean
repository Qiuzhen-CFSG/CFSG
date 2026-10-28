module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Setup
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Geometry

/-!
# The evaluation form on the literal doubled orbit

The chosen natural-plus-dual marking pulls evaluation back to W. Its polar
form is nondegenerate and dim W = 2n. Thus the nonsingular-centralizer
conclusion of 12.1.1 implies the actual global r-bound in 12.1.2(2).
The improved bound consumes precisely the nondegenerate fixed spaces of
12.1.9, whose construction remains with the odd-centralizer argument.

Source: Aschbacher--Smith, H.9.1(1), 12.1.2 and 12.1.9(3), pp.389,789,794.
-/

@[expose] public noncomputable section
open Module Subgroup Theory.GroupTheory BinaryNaturalDual
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n) [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
include B

/-- The linear form of the original multiplicative coordinates on W. -/
def linearCoordinates : Additive (componentOrbit V (T : Subgroup G)) ≃ₗ[ZMod 2]
    CoordinateSpace n :=
  let e : Additive (componentOrbit V (T : Subgroup G)) ≃+ CoordinateSpace n := {
    toFun w := (B.coordinates w.toMul).toAdd
    invFun v := Additive.ofMul (B.coordinates.symm (Multiplicative.ofAdd v))
    left_inv w := congrArg Additive.ofMul (B.coordinates.symm_apply_apply w.toMul)
    right_inv v := congrArg Multiplicative.toAdd
      (B.coordinates.apply_symm_apply (Multiplicative.ofAdd v))
    map_add' v w := congrArg Multiplicative.toAdd (B.coordinates.map_mul v.toMul w.toMul) }
  e.toLinearEquiv (ZMod.map_smul e)

theorem finrank_eq :
    finrank (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) = 2 * n := by
  rw [B.linearCoordinates.finrank_eq]
  simp [CoordinateSpace, Space, Module.finrank_prod, BinaryLinear.OuterCyclic.Space, two_mul]

/-- The source quadratic form on W, with the same natural and dual markings. -/
def quadratic : QuadraticForm (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) :=
  BinaryNaturalDual.quadratic.comp B.linearCoordinates.toLinearMap

@[simp] theorem quadratic_apply (w : componentOrbit V (T : Subgroup G)) :
    B.quadratic (Additive.ofMul w) = (B.coordinates w).toAdd.2 (B.coordinates w).toAdd.1 := rfl

theorem polar_nondegenerate : B.quadratic.polarBilin.Nondegenerate := by
  rw [quadratic, QuadraticMap.polarBilin_comp]
  constructor
  · intro x hx
    apply B.linearCoordinates.injective
    rw [map_zero]
    apply BinaryNaturalDual.polar_nondegenerate.1
    intro y
    obtain ⟨z, rfl⟩ := B.linearCoordinates.surjective y
    exact hx z
  · intro x hx
    apply B.linearCoordinates.injective
    rw [map_zero]
    apply BinaryNaturalDual.polar_nondegenerate.2
    intro y
    obtain ⟨z, rfl⟩ := B.linearCoordinates.surjective y
    exact hx z

/-- The exact earlier source assertion 12.1.1 to be supplied in this slice. -/
def NonsingularCentralizers : Prop :=
  ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) ≠ 0 →
    centralizer ({(w : G)} : Set G) ≤ normalizer (L : Set G)

/-- The pure-vector intersection implication of 12.1.6(2), with an actual
conjugate of W. Identity is excluded explicitly. -/
def PureIntersectionCentralizes : Prop :=
  ∀ (g : G) (w : componentOrbit V (T : Subgroup G)), w ≠ 1 →
    (B.coordinates w).toAdd.2 = 0 →
    (w : G) ∈ (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom →
    ⁅componentOrbit V (T : Subgroup G),
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ = ⊥

/-- The fixed space of an actual ambient actor X in the doubled orbit. -/
def fixedSpace (_B : DoubledBranch T L V n) (X : Subgroup G) :
    Submodule (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) :=
  subgroupSpace (componentOrbit V (T : Subgroup G)) (centralizer (X : Set G))

/-- The exact odd-actor geometry used in the last paragraph of 12.1.9.
The actor lies in M, fixes U, and acts nontrivially on W. -/
def OddFixedSpaces : Prop :=
  ∀ U : Subgroup G, U ≤ componentOrbit V (T : Subgroup G) →
    ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
    ∃ X : Subgroup G, Odd (Nat.card X) ∧ X ≤ normalizer (L : Set G) ∧
      ¬ X ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      X ≤ centralizer (U : Set G) ∧
      (B.quadratic.comp (B.fixedSpace X).subtype).polarBilin.Nondegenerate ∧
      4 ≤ finrank (ZMod 2) ((Additive (componentOrbit V (T : Subgroup G))) ⧸ B.fixedSpace X)

/-- Source 12.1.2(2), once 12.1.1 has been proved on the original orbit. -/
theorem globalR_ge [Finite G]
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hcentral : B.NonsingularCentralizers) :
    (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) := by
  apply globalR_ge_of_escape_codimension _ _ hNM n
  intro U _ hesc
  have hb := twice_finrank_le_of_totally_singular B.quadratic B.polar_nondegenerate
    (subgroupSpace (componentOrbit V (T : Subgroup G)) U)
    (singular_of_centralizer_escape _ _ U B.quadratic hcentral hesc)
  have hd := Submodule.finrank_quotient_add_finrank
    (subgroupSpace (componentOrbit V (T : Subgroup G)) U)
  rw [B.finrank_eq] at hb hd
  omega

/-- Source 12.1.9(3) from the actual odd fixed spaces, ready for 12.1.10. -/
theorem globalR_ge_add_two [Finite G]
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hcentral : B.NonsingularCentralizers) (hfixed : B.OddFixedSpaces) :
    ((n + 2 : ℕ) : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) := by
  apply globalR_ge_of_fixed_spaces _ _ B.quadratic n B.finrank_eq hNM hcentral
  intro U hUW hesc
  obtain ⟨X, _, _, _, hXU, hQ, hd⟩ := hfixed U hUW hesc
  refine ⟨B.fixedSpace X, ?_, hQ, hd⟩
  intro u hu
  apply (mem_subgroupSpace _ _ u).mpr
  exact (le_centralizer_iff.mp hXU) ((mem_subgroupSpace _ _ u).mp hu)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
