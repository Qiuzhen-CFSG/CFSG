module
public import Theory.Representation.CubicClifford.Dimension
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupAction.NoncentralTwoChiefLength
/-!
# Binary chief constituents detected by a cubic quotient

A normal two-kernel acts trivially on a simple binary representation. After
descent, a normal subgroup of order three with two-group quotient has no
nonzero fixed vector and the simple module has dimension two. The group-action
corollary retains the actual cubic subgroup and gives fixed index four.

Source application: Aschbacher–Smith 13.7.10(8), printed p.942, comparing
chief factors below the shared two-group in the S₃ and A₄ local groups.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace NoncentralChiefRefinement.CubicComparison
variable {H K V : Type*} [Group H] [Finite H] [Group K] [Finite K]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem trivial_of_two_group (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ] (hH : IsPGroup 2 H) : ρ = 1 := by
  have hk := normal_p_subgroup_le_ker ρ (⊤ : Subgroup H) (hH.to_subgroup ⊤)
  exact MonoidHom.ext (fun h => hk (mem_top h))

/-- A simple nontrivial binary representation above a normal cubic subgroup
has dimension two and no cubic fixed vector. -/
theorem cubic_quotient_simple (ρ : Representation (ZMod 2) K V)
    [IsIrreducible ρ] (X : Subgroup K) [X.Normal]
    (hX : Nat.card X = 3) (hq : IsPGroup 2 (K ⧸ X)) (hne : ρ ≠ 1) :
    Module.finrank (ZMod 2) V = 2 ∧ invariants (ρ.comp X.subtype) = ⊥ := by
  have hm : ¬ X ≤ ρ.ker := by
    intro hk
    let σ := quotientOfLEKer ρ X hk
    let : IsIrreducible σ := (quotientOfLEKer_irreducible_iff ρ X hk).mpr inferInstance
    have ht : σ = 1 := trivial_of_two_group σ hq
    apply hne
    have he := congrArg (fun τ : Representation (ZMod 2) (K ⧸ X) V =>
      τ.comp (QuotientGroup.mk' X)) ht
    exact he
  refine ⟨CubicClifford.finrank_eq_two ρ ⊥ X hX bot_le ?_ hm, ?_⟩
  · exact hq.of_equiv (QuotientGroup.quotientMulEquivOfEq (by simp : X = ⊥ ⊔ X))
  · by_contra hn
    exact hm (le_ker_of_normal_invariants_ne_bot ρ X hn)

/-- Descending through the actual normal two-kernel preserves the simple
binary action and identifies the fixed space of a marked cubic actor. -/
theorem simple_above_two_kernel (f : H →* K) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (X : Subgroup K) [X.Normal]
    (hX : Nat.card X = 3) (hq : IsPGroup 2 (K ⧸ X))
    (A : Subgroup H) (hAX : A.map f = X)
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ] (hne : ρ ≠ 1) :
    Module.finrank (ZMod 2) V = 2 ∧ invariants (ρ.comp A.subtype) = ⊥ := by
  have hk : f.ker ≤ ρ.ker := normal_p_subgroup_le_ker ρ f.ker hp
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let σ := (quotientOfLEKer ρ f.ker hk).comp e.symm.toMonoidHom
  have he (h : H) : σ (f h) = ρ h := by
    change quotientOfLEKer ρ f.ker hk (e.symm (f h)) = _
    have hh : e.symm (f h) = QuotientGroup.mk' f.ker h :=
      e.symm_apply_eq.mpr rfl
    rw [hh]
    rfl
  have hcomp : σ.comp f = ρ := MonoidHom.ext he
  let : IsIrreducible σ := (irreducible_comp_surjective_iff f hf σ).mp
    (hcomp ▸ (inferInstance : IsIrreducible ρ))
  have hnσ : σ ≠ 1 := by
    intro hs
    apply hne
    rw [← hcomp, hs]
    rfl
  obtain ⟨hd, hfix⟩ := cubic_quotient_simple σ X hX hq hnσ
  refine ⟨hd, ?_⟩
  apply le_antisymm _ bot_le
  intro v hv
  have hvX : v ∈ invariants (σ.comp X.subtype) := by
    rintro ⟨x,hx⟩
    rw [← hAX] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    change σ (f a) v = v
    rw [he]
    exact hv ⟨a,ha⟩
  rwa [hfix] at hvX

section GroupModule
variable {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    [MulDistribMulAction H W] [Nontrivial W]

/-- Each noncentral irreducible binary group section has cubic length one,
under the literal marked action above a normal cubic quotient. -/
theorem simple_group_length_one (f : H →* K) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (X : Subgroup K) [X.Normal]
    (hX : Nat.card X = 3) (hq : IsPGroup 2 (K ⧸ X))
    (A : Subgroup H) (hAX : A.map f = X)
    (hirr : ∀ D : Subgroup W, (∀ h : H, ∀ w : W, w ∈ D → h • w ∈ D) →
      D = ⊥ ∨ D = ⊤)
    (hne : ¬ ∀ h : H, ∀ w : W, h • w = w) : FixedPoints.cubicLength A W = 1 := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := H) (G := W) (p := 2)
  let : IsIrreducible ρ := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, ?_⟩
    intro U
    let D : Subgroup W := AddSubgroup.toSubgroup' U.toSubmodule.toAddSubgroup
    rcases hirr D (fun h w hw => U.apply_mem_toSubmodule h hw) with hd | hd
    · left
      apply bot_unique
      intro v hv
      have hh : v.toMul ∈ D := hv
      rw [hd, Subgroup.mem_bot] at hh
      exact hh
    · right
      apply top_unique
      intro v _
      have hv : v.toMul ∈ D := by rw [hd]; trivial
      exact hv
  have hnρ : ρ ≠ 1 := by
    intro he
    apply hne
    intro h w
    have hh := congrArg (fun τ : Representation (ZMod 2) H (Additive W) =>
      τ h (Additive.ofMul w)) he
    exact hh
  obtain ⟨hd, hfix⟩ := simple_above_two_kernel f hf hp X hX hq A hAX ρ hnρ
  have hc : Nat.card W = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod, hd] at hh
    exact hh
  have hbot : FixedPoints.subgroup A W = ⊥ := by
    apply le_bot_iff.mp
    intro w hw
    have hh : Additive.ofMul w ∈ invariants (ρ.comp A.subtype) := hw
    rwa [hfix, Submodule.mem_bot] at hh
  simp only [FixedPoints.cubicLength, hbot, Subgroup.index_bot, hc]
  decide
end GroupModule
end NoncentralChiefRefinement.CubicComparison

