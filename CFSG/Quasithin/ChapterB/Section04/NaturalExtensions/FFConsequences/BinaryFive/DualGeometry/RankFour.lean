module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Contracts
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Bounds
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Parabolics
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.QuadraticTwoCosts

/-!
# The rank-four dual geometry in B.4.9

The two factor costs equal two. Displacement therefore fills the four-space
of maps from the fixed-space quotient to the commutator space, giving a
common-axis four-group on the literal quotient, quadratic upstairs.

For the end-node placement, choose a fixed vector outside the two-dimensional
commutator space and a functional annihilating that space but not the vector.
Its kernel and the fixed line are complementary invariant four- and one-spaces.
Transport retains the original natural marking. This places the actor itself
in the block stabilizer; it makes no containment assertion about the order-256
flag radical. The block stabilizer's relative complement and faithful full
restriction action are separate group-geometric obligations.

Source: Aschbacher–Smith, B.4.9(2)(i),(iv), printed pp.94–95,
combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource BinaryLinear BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  [FiniteDimensional (ZMod 2) V]

private theorem costs_swap (d : DoubleNatural F 5 ρ)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (A : Subgroup G) :
    fixedCodim d.space.quotientRepresentation.dual A =
      fixedCodim d.space.toRepresentation A := by
  let f := (Module.evalEquiv (ZMod 2) d.space.toSubmodule).trans e.toLinearEquiv.dualMap
  have he (g : G) (v : d.space.toSubmodule) :
      f (d.space.toRepresentation g v) = d.space.quotientRepresentation.dual g (f v) := by
    apply LinearMap.ext
    intro w
    change e w (d.space.toRepresentation g v) =
      e (d.space.quotientRepresentation g⁻¹ w) v
    have h := congrArg (fun l : Module.Dual (ZMod 2) d.space.toSubmodule => l v)
      (LinearMap.congr_fun (e.isIntertwining' g⁻¹) w)
    change e (d.space.quotientRepresentation g⁻¹ w) v =
      e w (d.space.toRepresentation ((g⁻¹)⁻¹) v) at h
    simpa only [inv_inv] using h.symm
  simpa only [Subgroup.map_id] using
    (fixedCodim_map_equivariant d.space.toRepresentation
      d.space.quotientRepresentation.dual (MonoidHom.id G) f he A).symm

private theorem invariant_four_plus_one
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (σ : Representation (ZMod 2) G X) (hdim : Module.finrank (ZMod 2) X = 5)
    (A : Subgroup G) (hc : fixedCodim σ A = 2) (hd : fixedCodim σ.dual A = 2) :
    ∃ W K : Submodule (ZMod 2) X,
      Module.finrank (ZMod 2) W = 4 ∧ Module.finrank (ZMod 2) K = 1 ∧
      IsCompl W K ∧
      (∀ g ∈ A, ∀ x, σ g x ∈ W ↔ x ∈ W) ∧
      (∀ g ∈ A, ∀ x ∈ K, σ g x = x) := by
  let C := fixedSpace σ A
  let D := Coinvariants.ker (σ.comp A.subtype)
  have hC : Module.finrank (ZMod 2) C = 3 := by
    have h := fixedCodim_add_finrank σ A
    change Module.finrank (ZMod 2) (fixedSpace σ A) = 3
    omega
  have hD : Module.finrank (ZMod 2) D = 2 :=
    (finrank_dual_quotient_invariants (σ.comp A.subtype)).symm.trans hd
  have hn : ¬ C ≤ D := by
    intro h
    have := Submodule.finrank_mono h
    omega
  obtain ⟨v, hvC, hvD⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨f, hfv, hDf⟩ := D.exists_le_ker_of_notMem hvD
  have hf : f ≠ 0 := by intro h; apply hfv; simp [h]
  have hv : v ≠ 0 := by intro h; apply hvD; rw [h]; exact D.zero_mem
  let K := Submodule.span (ZMod 2) {v}
  have hK : Module.finrank (ZMod 2) K = 1 := finrank_span_singleton hv
  have hWK : IsCompl f.ker K :=
    Module.Dual.isCompl_ker_of_disjoint_of_ne_bot hf
      (Submodule.disjoint_span_singleton_of_notMem hfv)
      (Submodule.span_singleton_eq_bot.not.mpr hv)
  have hW : Module.finrank (ZMod 2) f.ker = 4 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  refine ⟨f.ker, K, hW, hK, hWK, ?_, ?_⟩
  · intro g hg x
    have hx := hDf (Coinvariants.sub_mem_ker (ρ := σ.comp A.subtype) ⟨g, hg⟩ x)
    change f (σ g x - x) = 0 at hx
    rw [map_sub, sub_eq_zero] at hx
    change f (σ g x) = 0 ↔ f x = 0
    rw [hx]
  · have hKC : K ≤ C := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvC)
    intro g hg x hx
    exact hKC hx ⟨g, hg⟩

/-- The rank-four actor preserves a four-space and fixes a complementary line
under the original natural marking. Only the actor is placed in this Levi. -/
theorem dual_rank_four_block_placement (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hr : rank A = 4) :
    ∃ W K : Submodule (ZMod 2) (Space 5),
      Module.finrank (ZMod 2) W = 4 ∧ Module.finrank (ZMod 2) K = 1 ∧
      IsCompl W K ∧ A.map (groupEquiv d hF).toMonoidHom ≤ endNodeLevi W K := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  obtain ⟨hc, hd, _⟩ := d.dual_rank_four_costs e (hA.isOffender ρ) hr
  have hd' : fixedCodim d.space.toRepresentation.dual A = 2 := by
    have he := fixedCodim_map_equivariant d.space.quotientRepresentation
      d.space.toRepresentation.dual (MonoidHom.id G) e.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A
    simpa only [Subgroup.map_id, hd] using he.symm
  have hdim : Module.finrank (ZMod 2) d.space.toSubmodule = 5 := by
    rw [(coordinates d hF).linearEquiv.finrank_eq]
    change Module.finrank (ZMod 2) (Space 5) = 5
    simp [Space]
  obtain ⟨W, K, hW, hK, hWK, hWA, hKA⟩ :=
    invariant_four_plus_one d.space.toRepresentation hdim A hc hd'
  let c : d.space.toSubmodule ≃ₗ[ZMod 2] Space 5 := (coordinates d hF).linearEquiv
  refine ⟨W.map c.toLinearMap, K.map c.toLinearMap,
    (c.finrank_map_eq W).trans hW, (c.finrank_map_eq K).trans hK,
    (Submodule.orderIsoMapComap c).isCompl_iff.mp hWK, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hmem (S : Submodule (ZMod 2) d.space.toSubmodule) (x : Space 5) :
      x ∈ S.map c.toLinearMap ↔ c.symm x ∈ S := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨c.symm x, hx, c.apply_symm_apply x⟩
  have he (x : Space 5) : c.symm ((groupEquiv d hF).toMonoidHom a x) =
      d.space.toRepresentation a (c.symm x) := by
    apply c.injective
    rw [c.apply_symm_apply]
    have h : c (d.space.toRepresentation a (c.symm x)) =
        (groupEquiv d hF).toMonoidHom a (c (c.symm x)) := intertwines d hF a (c.symm x)
    rw [c.apply_symm_apply] at h
    exact h.symm
  constructor
  · intro x
    rw [hmem, he, hmem]
    exact hWA a ha (c.symm x)
  · intro x
    rw [hmem, he, hmem]
    constructor
    · intro hx
      have h := hKA a⁻¹ (A.inv_mem ha) _ hx
      have h' : c.symm x = d.space.toRepresentation a (c.symm x) := by
        simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] using h
      rwa [h']
    · intro hx
      rw [hKA a ha _ hx]
      exact hx
end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {F : BinaryField} {ρ : Representation (ZMod 2) G V}

/-- Rank four supplies the four-group on the literal quotient before any splitting. -/
theorem dual_rank_four_axis (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hr : rank A = 4) :
    ∃ E : Subgroup G, E ≤ A ∧ QuadraticSplitting.IsAxisFour d E ∧ IsQuadratic ρ E := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  have hq := d.dual_rank_four_quadratic e hA hr
  obtain ⟨hn, hc, _⟩ := d.dual_rank_four_costs e (hA.isOffender ρ) hr
  have hd : fixedCodim d.space.quotientRepresentation.dual A = 2 :=
    (costs_swap d e A).trans hn
  have hq' : IsQuadratic d.space.quotientRepresentation A :=
    quadratic_of_equivariant_surjection ρ d.space.quotientRepresentation
      d.space.toSubmodule.mkQ d.space.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hq
  obtain ⟨E, hEA, he, hcard, I, hI, hfix⟩ :=
    QuadraticTwoCosts.axis_of_two_costs d.space.quotientRepresentation
      d.quotient_faithful A hA.1 hr hq' hc hd
  exact ⟨E, hEA, ⟨he, hcard, I, hI.trans hF.symm, hfix⟩,
    fun a ha b hb v => hq a (hEA ha) b (hEA hb) v⟩
end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
