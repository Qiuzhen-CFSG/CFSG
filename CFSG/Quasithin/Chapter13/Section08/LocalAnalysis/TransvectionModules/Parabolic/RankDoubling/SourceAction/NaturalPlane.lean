module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Actions

/-!
# The marked natural plane in the doubling argument

The actual natural binary S₃-module is the even-weight subspace on three
letters. Its cubic satisfies r²v = v + rv, and every nonzero v and rv
span it. The calculation is finite and checked by the kernel. A compatible
linear isomorphism from the literal V/V₂ transfers these identities to the
image of V in U₂/V₂. No dimension or decomposition of U₂ is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and the natural parabolic action used in 13.8.6, p.948.
-/

public section

open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction

abbrev NaturalPlane := BinaryPermutation.core (Fin 3)

private local instance : DecidablePred
    (fun v : BinaryPermutation.Full (Fin 3) => v ∈ NaturalPlane) :=
  fun _ => inferInstanceAs (Decidable (_ = (0 : F)))

private local instance : Fintype NaturalPlane :=
  Fintype.ofFinset (Finset.univ.filter (fun v => v ∈ NaturalPlane)) (by simp)

theorem natural_cubic_polynomial (v : NaturalPlane) :
    BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic
      (BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v) =
    v + BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v := by
  revert v
  decide +kernel

private theorem natural_four_vectors (v : NaturalPlane) (hv : v ≠ 0)
    (w : NaturalPlane) :
    w = 0 ∨ w = v ∨
      w = BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v ∨
      w = v + BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v := by
  revert w hv v
  decide +kernel

/-- Every nonzero vector of the natural module and its cubic image span the module. -/
theorem natural_pair_spans (v : NaturalPlane) (hv : v ≠ 0) (w : NaturalPlane) :
    w ∈ Submodule.span F
      {v, BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v} := by
  have hv' : v ∈ Submodule.span F
      {v, BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v} :=
    Submodule.subset_span (by simp)
  have hr : BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v ∈
      Submodule.span F
        {v, BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic v} :=
    Submodule.subset_span (by simp)
  rcases natural_four_vectors v hv w with rfl | rfl | rfl | rfl
  · exact Submodule.zero_mem _
  · exact hv'
  · exact hr
  · exact Submodule.add_mem _ hv' hr

variable {G : Type*} [Group G]
variable (H V V₂ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

/-- The source plane before inclusion into the larger quotient. -/
abbrev SeedQuotient := V ⧸ V₂.subgroupOf V

def seedClass (v : V) : Additive (SeedQuotient V V₂) :=
  Additive.ofMul (QuotientGroup.mk' (V₂.subgroupOf V) v)

omit [IsMulCommutative (Source.VH H V)] in
/-- Evaluate the seed class without exposing the implementation across modules. -/
theorem seedClass_eq_mk (v : V) :
    seedClass V V₂ v = Additive.ofMul (QuotientGroup.mk' (V₂.subgroupOf V) v) := by rfl

def seedInclusion : Additive (SeedQuotient V V₂) →ₗ[F] Additive (Uhat H V V₂) :=
  (QuotientGroup.map (V₂.subgroupOf V) (V₂.subgroupOf (Source.U2 H V V₂))
    (inclusion (Source.seed_le_U2 H V V₂)) (fun _ hx => hx)).toAdditive.toZModLinearMap 2

theorem seedInclusion_mk (v : V) :
    seedInclusion H V V₂ (seedClass V V₂ v) = seedVector H V V₂ v := by rfl

/-- A source vector outside V₂ has nonzero class under any genuine model isomorphism. -/
theorem marked_seed_ne_zero
    (e : Additive (SeedQuotient V V₂) ≃ₗ[F] NaturalPlane)
    (a : V) (ha : (a : G) ∉ V₂) : e (seedClass V V₂ a) ≠ 0 := by
  intro he
  have hz : seedClass V V₂ a = 0 := e.injective (he.trans e.map_zero.symm)
  exact ha ((QuotientGroup.eq_one_iff a).mp hz)

/-- Transfer the two natural-plane identities through the literal quotient inclusion.
The compatibility input is an intertwining equation for the marked source action,
not a polynomial, spanning, or dimension assumption. -/
theorem marked_seed_facts
    (e : Additive (SeedQuotient V V₂) ≃ₗ[F] NaturalPlane)
    (R : Additive (Uhat H V V₂) →ₗ[F] Additive (Uhat H V V₂))
    (he : ∀ b : V, R (seedVector H V V₂ b) =
      seedInclusion H V V₂
        (e.symm (BinaryPermutation.coreRepresentation (Fin 3)
          InvertedCubicTensor.cubic (e (seedClass V V₂ b)))))
    (a : V) (ha : (a : G) ∉ V₂) :
    R (R (seedVector H V V₂ a)) =
        seedVector H V V₂ a + R (seedVector H V V₂ a) ∧
      ∀ b : V, seedVector H V V₂ b ∈ Submodule.span F
        {seedVector H V V₂ a, R (seedVector H V V₂ a)} := by
  let f := (seedInclusion H V V₂).comp e.symm.toLinearMap
  let r := BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic
  have hf (x : NaturalPlane) : R (f x) = f (r x) := by
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (V₂.subgroupOf V) (e.symm x).toMul
    have hb' : seedClass V V₂ b = e.symm x := congrArg Additive.ofMul hb
    have hfx : f x = seedVector H V V₂ b := by
      change seedInclusion H V V₂ (e.symm x) = _
      rw [← hb', seedInclusion_mk]
    rw [hfx, he]
    simp only [hb', e.apply_symm_apply]
    rfl
  let v := e (seedClass V V₂ a)
  have hv : v ≠ 0 := marked_seed_ne_zero V V₂ e a ha
  have hfv : f v = seedVector H V V₂ a := by
    change seedInclusion H V V₂ (e.symm (e (seedClass V V₂ a))) = _
    rw [e.symm_apply_apply, seedInclusion_mk]
  constructor
  · rw [← hfv, hf, hf, natural_cubic_polynomial, map_add]
  · intro b
    have hle : Submodule.span F {v, r v} ≤
        (Submodule.span F {f v, R (f v)}).comap f := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact Submodule.subset_span (by simp)
      · have hx' : x = r v := Set.mem_singleton_iff.mp hx
        subst x
        change f (r v) ∈ Submodule.span F {f v, R (f v)}
        rw [← hf]
        exact Submodule.subset_span (by simp)
    have hm := hle (natural_pair_spans v hv (e (seedClass V V₂ b)))
    change f (e (seedClass V V₂ b)) ∈ Submodule.span F {f v, R (f v)} at hm
    have hb : f (e (seedClass V V₂ b)) = seedVector H V V₂ b := by
      change seedInclusion H V V₂ (e.symm (e (seedClass V V₂ b))) = _
      rw [e.symm_apply_apply, seedInclusion_mk]
    rwa [hb, hfv] at hm

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
