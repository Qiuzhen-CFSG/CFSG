module

public import Theory.Representation.BinaryOffender.MarkedOrbitCore
public import Theory.LinearAlgebra.AlternatingPlane
public import Theory.GroupTheory.PrimeRankWitness

/-!
# The original symplectic hypotheses of G.10

The action, alternating form, marked vector, isotropic space and elementary
actor are literal data. The smaller actor is a subgroup of X, so X/X₀ is the
actual relative quotient. Full transvection action means equality with all
centered transvections, expressed by their entire linear functionals.

Source: Aschbacher--Smith, G.10.1--2, printed p.357.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The pointwise stabilizer of the marked binary point. -/
def pointCentralizer (ρ : Representation (ZMod 2) G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ a v = v at ha
    change ρ b v = v at hb
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change ρ a⁻¹ v = v
    have he := congrArg (ρ a⁻¹) ha
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using he.symm

/-- G.10.1, with the source action and its original marked subgroups. -/
structure Hypothesis [Finite G] (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) [IsElementaryAbelian 2 X] (X₀ : Subgroup X) : Prop where
  faithful : Function.Injective ρ
  alternating : B.IsAlt
  nondegenerate : B.Nondegenerate
  preserves : ∀ g u w, B (ρ g u) (ρ g w) = B u w
  point_ne_zero : v ≠ 0
  point_mem : v ∈ W
  isotropic : ∀ u ∈ W, ∀ w ∈ W, B u w = 0
  fixes_point : X ≤ pointCentralizer ρ v
  orbit_span : Submodule.span (ZMod 2) {w | ∃ g : G, ρ g v = w} = ⊤
  odd_index : Odd (pointCentralizer ρ v).index
  dimension : finrank (ZMod 2) W + Group.rank (X ⧸ X₀) = finrank (ZMod 2) V - 1
  displacement : ∀ x : X, ∀ u, B v u = 0 → ρ x u - u ∈ W
  fixed_bound : ∀ x : X, x ∉ X₀ → ∀ u, ρ x u = u → B v u = 0
  transvections : ∀ x : X, ∃ f : Module.Dual (ZMod 2) W,
    f ⟨v, point_mem⟩ = 0 ∧ ∀ w : W, ρ x w = (w : V) + f w • v
  full_transvections : ∀ f : Module.Dual (ZMod 2) W, f ⟨v, point_mem⟩ = 0 →
    ∃ x : X, ∀ w : W, ρ x w = (w : V) + f w • v

namespace Hypothesis
variable [Finite G] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- Source G.10.2 retains the exact quotient rank and ambient two-rank. -/
theorem dimension_bound :
    finrank (ZMod 2) V ≤ 2 * (Group.rank (X ⧸ X₀) + 1) ∧
      2 * (Group.rank (X ⧸ X₀) + 1) ≤ 2 * (primeRank 2 G + 1) := by
  have hi := B.twice_finrank_le_of_isotropic h.nondegenerate W h.isotropic
  have hp : 0 < finrank (ZMod 2) V := by
    let : Nontrivial V := ⟨⟨v, 0, h.point_ne_zero⟩⟩
    exact Module.finrank_pos
  have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans
      (X.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 X))
  have hd := h.dimension
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- Every actor in X preserves the actual isotropic marked space. -/
theorem stable_W (x : X) (w : V) (hw : w ∈ W) : ρ x w ∈ W := by
  obtain ⟨f, _, hf⟩ := h.transvections x
  rw [hf ⟨w, hw⟩]
  exact W.add_mem hw (W.smul_mem _ h.point_mem)

omit [FiniteDimensional (ZMod 2) V] in
/-- Orbit generation excludes the marked point from every proper submodule. -/
theorem point_not_mem (U : Subrepresentation ρ) (hU : U.toSubmodule ≠ ⊤) : v ∉ U := by
  intro hv
  apply hU
  apply top_unique
  rw [← h.orbit_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact U.apply_mem_toSubmodule g hv

end Hypothesis
end CFSG.Quasithin.ChapterG.Section10
