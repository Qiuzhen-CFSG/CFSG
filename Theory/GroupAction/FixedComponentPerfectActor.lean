module
public import Theory.GroupAction.CommutingFixedComponentFixer
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# Perfect actors centralize a component with a small pointwise fixer

The actual normalizer action commutes with the marked actor and fixes its component pointwise. Its image has order at most two. Perfectness puts the entire actor group in the literal action kernel, which is the containing-component centralizer.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut

/-- The literal pointwise component-fixer bound annihilates every perfect
homomorphic actor, without choosing a containing subgroup model. -/
theorem perfect_fixed_component_action_eq_one
    {A E : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [Group E] [Finite E]
    (a : MulAut E) (B : Subgroup a.fixedSubgroup) (f : A →* MulAut E)
    (hcomm : ∀ c : A, Commute (f c) a)
    (hfix : ∀ (c : A) (x : B), f c (((x : a.fixedSubgroup) : E)) = x)
    (hcard : Nat.card (commutingFixedComponentFixer a B) ≤ 2) : f = 1 := by
  have hfrange : f.range ≤ commutingFixedComponentFixer a B := by
    rintro _ ⟨c,rfl⟩
    refine ⟨mem_centralizer_singleton_iff.mpr (hcomm c), ?_⟩
    rintro ⟨x,⟨y,hy,rfl⟩⟩
    exact hfix c ⟨y,hy⟩
  have hindex : f.ker.index ≤ 2 := by
    rw [index_ker]
    exact (card_le_of_le hfrange).trans hcard
  have hker : f.ker = ⊤ :=
    top_unique (le_of_isPerfect_of_index_le_two ⊤ f.ker hindex)
  apply MonoidHom.ext
  intro c
  change c ∈ f.ker
  rw [hker]
  trivial

variable {G : Type*} [Group G] [Finite G]

/-- A perfect pointwise actor in a two-element fixed-component fixer
centralizes the entire containing group. -/
theorem perfect_fixed_component_actor_centralizes
    (X C : Subgroup G) [Group.IsPerfect C]
    (hCN : C ≤ normalizer (X : Set G))
    (t : G) (a : MulAut X)
    (hact : ∀ x : X, (a x : G) = t * (x : G) * t⁻¹)
    (B : Subgroup a.fixedSubgroup)
    (hCt : C ≤ centralizer ({t} : Set G))
    (hCB : ∀ c ∈ C, ∀ x : B,
      c * (((x : a.fixedSubgroup) : X) : G) = (((x : a.fixedSubgroup) : X) : G) * c)
    (hcard : Nat.card (commutingFixedComponentFixer a B) ≤ 2) :
    C ≤ centralizer (X : Set G) := by
  let f : C →* MulAut X := X.normalizerMonoidHom.comp (inclusion hCN)
  have hf (c : C) (x : X) : (f c x : G) = (c : G) * (x : G) * (c : G)⁻¹ := rfl
  have hfrange : f.range ≤ commutingFixedComponentFixer a B := by
    rintro _ ⟨c, rfl⟩
    constructor
    · apply mem_centralizer_singleton_iff.mpr
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change ((f c) (a x) : G) = (a ((f c) x) : G)
      rw [hf, hact, hact, hf]
      have hct : (c : G) * t = t * (c : G) :=
        mem_centralizer_singleton_iff.mp (hCt c.property)
      calc
        _ = ((c : G) * t) * (x : G) * ((c : G) * t)⁻¹ := by group
        _ = (t * (c : G)) * (x : G) * (t * (c : G))⁻¹ := by rw [hct]
        _ = _ := by group
    · rintro ⟨x, ⟨y, hy, rfl⟩⟩
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hCB c c.property ⟨y,hy⟩)
  have hindex : f.ker.index ≤ 2 := by
    rw [index_ker]
    exact (card_le_of_le hfrange).trans hcard
  have hker : f.ker = ⊤ :=
    top_unique (le_of_isPerfect_of_index_le_two ⊤ f.ker hindex)
  intro c hc x hx
  have he : f ⟨c,hc⟩ = 1 := by
    change (⟨c,hc⟩ : C) ∈ f.ker
    rw [hker]
    trivial
  have hh := congrArg (fun b : MulAut X => (b ⟨x,hx⟩ : G)) he
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end MulAut
