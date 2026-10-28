module

public import Theory.Representation.FirstCohomologyG2Natural.NonbinaryCoordinates
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic

/-!
# The moved plane of a binary G₂ long-root involution

We work in the full split-octonion automorphism group `Atlas.G2.Model (ZMod 2)`
and its actual six-dimensional natural quotient, not in its derived subgroup.
The moved space of `rootA 1` consists of the first two off-diagonal coordinates.
The explicit element `rootF 1 * weylS` centralizes this involution, has cube one,
and fixes no nonzero vector of the moved plane. Thus the plane stabilizer is
transitive on its three nonzero vectors.

This supplies the normalizer calculation implicit in Aschbacher–Smith,
*The Classification of Quasithin Groups*, proof of 6.2.19, printed p.691
(PDF p.708), for case G.11.2(6), printed p.364 (PDF p.375). Identification of
an arbitrary eligible involution with this conjugacy class is a separate result.
The root formulas and their octonion-automorphism proofs come from the licensed
ATLAS ports imported through `G2Natural`; no new ATLAS source is copied here.
-/

public section

open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit
open Atlas.G2.Natural Atlas.G2.Natural.Nonbinary

namespace Representation.RankTwo.GTwo
abbrev K := ZMod 2
abbrev G := Atlas.G2.Model K
abbrev V := Atlas.G2.Natural.Space K

/-- A concrete order-three element of the long-root centralizer. -/
@[expose] def cycleActor : G := rootF 1 * weylS

theorem cycleActor_commute : Commute cycleActor (rootA 1) := by
  change cycleActor * rootA 1 = rootA 1 * cycleActor
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [cycleActor, rootF, rootFEquiv, rootFLinear, rootFApply,
    rootA, rootAEquiv, rootALinear, rootAApply, weylS, weylSEquiv,
    weylSLinear, weylSApply, sub_eq_add_neg, CharTwo.neg_eq]
  ring

theorem cycleActor_cube : cycleActor ^ 3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [cycleActor, pow_succ, rootF, rootFEquiv, rootFLinear, rootFApply,
    weylS, weylSEquiv, weylSLinear, weylSApply, sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf <;>
    simp [show (2 : K) = 0 by decide, show (3 : K) = 1 by decide,
      show (4 : K) = 0 by decide, show (6 : K) = 0 by decide,
      show (9 : K) = 1 by decide]

/-- The centralizing cubic fixes no nonzero vector in the moved plane. -/
theorem cycleActor_fixed_moved_eq_zero (z : V)
    (hz : z ∈ movedSpace (action K) (rootA 1))
    (hc : action K cycleActor z = z) : z = 0 := by
  obtain ⟨w, rfl⟩ := hz
  change action K cycleActor (action K (rootA 1) w - w) =
    action K (rootA 1) w - w at hc
  change action K (rootA 1) w - w = 0
  obtain ⟨x, rfl⟩ := mk_surjective K w
  have h0 := congrArg (fun z => coordinates K z 0) hc
  have h1 := congrArg (fun z => coordinates K z 1) hc
  simp [cycleActor, action_mk,
    coordinates_mk, traceZeroAction_val, nonbinaryIndex,
    rootA, rootAEquiv, rootALinear, rootAApply,
    rootF, rootFEquiv, rootFLinear, rootFApply,
    weylS, weylSEquiv, weylSLinear, weylSApply,
    sub_eq_add_neg, CharTwo.neg_eq] at h0 h1
  have h6 : x.val 6 = 0 := by
    linear_combination (norm := (ring_nf; simp [show (2 : K) = 0 by decide])) h0 + h1
  have h7 : x.val 7 = 0 := by
    linear_combination (norm := (ring_nf; simp [show (2 : K) = 0 by decide])) h0
  apply coordinates_injective K
  ext i
  fin_cases i <;> simp [map_sub, action_mk, coordinates_mk, traceZeroAction_val,
    nonbinaryIndex, rootA, rootAEquiv, rootALinear, rootAApply, h6, h7]

private def planeLift : (Fin 2 → K) →ₗ[K] TraceZero K where
  toFun a := ⟨![a 0, a 1, 0, 0, 0, 0, 0, 0], by simp [trace]⟩
  map_add' := by intro a b; apply Subtype.ext; ext i; fin_cases i <;> simp
  map_smul' := by intro r a; apply Subtype.ext; ext i; fin_cases i <;> simp

/-- The first two off-diagonal coordinates, embedded into the natural quotient. -/
def planeEmbedding : (Fin 2 → K) →ₗ[K] V := (mk K).comp planeLift

@[simp] theorem coordinates_planeEmbedding (a : Fin 2 → K) (i : Fin 6) :
    coordinates K (planeEmbedding a) i = ![a 0, a 1, 0, 0, 0, 0] i := by
  fin_cases i <;> rfl

theorem planeEmbedding_injective : Function.Injective planeEmbedding := by
  intro a b h
  have h0 := congrArg (fun z => coordinates K z 0) h
  have h1 := congrArg (fun z => coordinates K z 1) h
  funext i
  fin_cases i
  · simpa [coordinates_planeEmbedding, Matrix.cons_val_zero, Matrix.cons_val_one] using h0
  · simpa [coordinates_planeEmbedding, Matrix.cons_val_zero, Matrix.cons_val_one] using h1

/-- The displacement image is exactly the explicit binary plane. -/
theorem movedSpace_rootA : movedSpace (action K) (rootA 1) = planeEmbedding.range := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := mk_surjective K w
    refine ⟨![x.val 6, x.val 7], ?_⟩
    change planeEmbedding ![x.val 6, x.val 7] = action K (rootA 1) (mk K x) - mk K x
    apply coordinates_injective K
    ext i
    fin_cases i <;>
      simp [action_mk, coordinates_mk, traceZeroAction_val,
        nonbinaryIndex, rootA, rootAEquiv, rootALinear, rootAApply,
        sub_eq_add_neg, CharTwo.neg_eq]
    all_goals ring_nf; simp [show (2 : K) = 0 by decide]
  · rintro ⟨a, rfl⟩
    refine ⟨mk K ⟨![0,0,0,0,0,0,a 0,a 1], by simp [trace]⟩, ?_⟩
    change action K (rootA 1) (mk K _) - mk K _ = planeEmbedding a
    apply coordinates_injective K
    ext i
    fin_cases i <;>
      simp [action_mk, coordinates_mk, traceZeroAction_val,
        nonbinaryIndex, rootA, rootAEquiv, rootALinear, rootAApply,
        sub_eq_add_neg, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem finrank_movedSpace_rootA : Module.finrank K (movedSpace (action K) (rootA 1)) = 2 := by
  rw [movedSpace_rootA, LinearMap.finrank_range_of_inj planeEmbedding_injective]
  simp

/-- The full G₂(2) stabilizer acts transitively on the nonzero moved vectors. -/
theorem stabilizerTransitive_rootA : StabilizerTransitive (action K)
    (movedSpace (action K) (rootA 1)) :=
  stabilizerTransitive_of_order_three (action K) (rootA 1) cycleActor
    finrank_movedSpace_rootA cycleActor_commute cycleActor_cube cycleActor_fixed_moved_eq_zero

theorem orderOf_rootA : orderOf (rootA (1 : K)) = 2 := by
  apply orderOf_eq_prime
  · simp [pow_two, Atlas.G2.rootA_add, CharTwo.add_self_eq_zero]
  · intro h
    exact one_ne_zero (rootA_injective (h.trans rootA_zero.symm))

end Representation.RankTwo.GTwo
