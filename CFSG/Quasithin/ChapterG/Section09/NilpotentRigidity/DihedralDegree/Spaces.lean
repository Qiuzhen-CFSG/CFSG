module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness

/-!
# The one-factor degree bounds and the dimensions of the splitting

The A.1.44 splitting makes the rotation-moved space the direct sum of two
isomorphic reflection half-spaces. Its rotation-fixed space is zero, so
the prime-order orbit congruence gives `p ∣ 2^(dim M) - 1`. In moved
dimension two this forces `p=3`; in moved dimension four it forces
`p=3` or `p=5`. In particular this excludes `p=7`, which a bound for
arbitrary cyclic actions in the ambient dimension would not exclude.

This proves the one-factor estimates used in Aschbacher--Smith G.9.2,
printed pp.351--353, with the genuine A.1.44 splitting kept as the
explicit earlier-theorem input. Trivial summands are allowed throughout.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree

open DihedralGroup

universe v

variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {p : ℕ} (σ : Representation (ZMod 2) (DihedralGroup p) W)

abbrev rotationFixed : Submodule (ZMod 2) W := LinearMap.ker (σ (r 1) - 1)
abbrev rotationMoved : Submodule (ZMod 2) W := movedSpace σ (Subgroup.zpowers (r 1))
abbrev reflectionHalf : Submodule (ZMod 2) W :=
  rotationMoved σ ⊓ LinearMap.ker (σ (sr 0) - 1)

theorem mem_rotationFixed (w : W) : w ∈ rotationFixed σ ↔ σ (r 1) w = w := by
  simp [rotationFixed, LinearMap.mem_ker, sub_eq_zero]

theorem rotationMoved_ne_bot (hp : p.Prime) (hf : Function.Injective σ) :
    rotationMoved σ ≠ ⊥ := by
  intro hb
  have he : σ (r 1) = σ 1 := by
    ext w
    have h := Representation.Coinvariants.sub_mem_ker
      (ρ := σ.comp (Subgroup.zpowers (r 1)).subtype)
      ⟨r 1, Subgroup.mem_zpowers _⟩ w
    change σ (r 1) w - w ∈ rotationMoved σ at h
    rw [hb, Submodule.mem_bot, sub_eq_zero] at h
    simpa using h
  have hh := congrArg orderOf (hf he)
  rw [orderOf_r_one, orderOf_one] at hh
  exact hp.ne_one hh

theorem split_dimensions [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v})
    (hp : p.Prime) (ho : Odd p) (hf : Function.Injective σ) :
    Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (rotationFixed σ) +
      2 * Module.finrank (ZMod 2) (reflectionHalf σ) ∧
    Module.finrank (ZMod 2) (rotationMoved σ) =
      2 * Module.finrank (ZMod 2) (reflectionHalf σ) ∧
    0 < Module.finrank (ZMod 2) (reflectionHalf σ) := by
  obtain ⟨hc, hd, he⟩ := split W p hp ho σ hf
  have hm := Submodule.finrank_sup_add_finrank_inf_eq
    (reflectionHalf σ) ((reflectionHalf σ).map (σ (r 1)))
  rw [he, hd.eq_bot, finrank_bot, add_zero] at hm
  have heq : Module.finrank (ZMod 2) ((reflectionHalf σ).map (σ (r 1))) =
      Module.finrank (ZMod 2) (reflectionHalf σ) :=
    (LinearEquiv.ofBijective (σ (r 1)) (σ.apply_bijective _)).finrank_map_eq _
  rw [heq] at hm
  have hpos : 0 < Module.finrank (ZMod 2) (rotationMoved σ) :=
    by
      have : Nontrivial (rotationMoved σ) :=
        Submodule.nontrivial_iff_ne_bot.mpr (rotationMoved_ne_bot σ hp hf)
      exact Module.finrank_pos
  have hc' := Submodule.finrank_add_eq_of_isCompl hc
  change Module.finrank (ZMod 2) (rotationFixed σ) +
    Module.finrank (ZMod 2) (rotationMoved σ) = _ at hc'
  change Module.finrank (ZMod 2) (rotationMoved σ) =
    Module.finrank (ZMod 2) (reflectionHalf σ) +
    Module.finrank (ZMod 2) (reflectionHalf σ) at hm
  omega

theorem coinvariants_stable {G : Type*} [Group G]
    (τ : Representation (ZMod 2) G W) (g : G) :
    Representation.Coinvariants.ker τ ≤
      (Representation.Coinvariants.ker τ).comap (τ g) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨s, w⟩, rfl⟩
  change τ g (τ s w - w) ∈ Representation.Coinvariants.ker τ
  have h := (Representation.Coinvariants.ker τ).sub_mem
    (Representation.Coinvariants.sub_mem_ker (g * s) w)
    (Representation.Coinvariants.sub_mem_ker g w)
  simpa [map_mul, Module.End.mul_apply] using h

theorem rotationMoved_card_modEq [FiniteDimensional (ZMod 2) W]
    (hp : p.Prime) (hc : Disjoint (rotationFixed σ) (rotationMoved σ)) :
    2 ^ Module.finrank (ZMod 2) (rotationMoved σ) ≡ 1 [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  let R := Subgroup.zpowers (r (1 : ZMod p))
  let τ := σ.comp R.subtype
  let M := rotationMoved σ
  let μ : Representation (ZMod 2) R M :=
    Representation.subrepresentation τ M (coinvariants_stable τ)
  let : MulAction R M :=
    { smul := fun g w => μ g w
      one_smul := by intro w; change μ 1 w = w; simp
      mul_smul := by intro g h w; change μ (g * h) w = μ g (μ h w); simp }
  have hR : Nat.card R = p := by
    rw [Nat.card_zpowers, orderOf_r_one]
  have hP : IsPGroup p R := IsPGroup.of_card (n := 1) (by simpa using hR)
  have hfix (w : MulAction.fixedPoints R M) : (w.val : W) = 0 := by
    have h := w.property (⟨r 1, Subgroup.mem_zpowers _⟩ : R)
    have h' : σ (r 1) (w.val : W) = (w.val : W) := congrArg Subtype.val h
    have hw : (w.val : W) ∈ rotationFixed σ ⊓ rotationMoved σ :=
      ⟨(mem_rotationFixed σ _).mpr h', w.val.property⟩
    rwa [hc.eq_bot, Submodule.mem_bot] at hw
  have : Unique (MulAction.fixedPoints R M) :=
    { default := ⟨0, by intro g; change μ g 0 = 0; exact map_zero _⟩
      uniq := by intro w; apply Subtype.ext; apply Subtype.ext; exact hfix w }
  let : Finite M := Module.finite_of_finite (ZMod 2)
  have h := hP.card_modEq_card_fixedPoints M
  rw [Nat.card_unique (α := MulAction.fixedPoints R M),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M), Nat.card_zmod] at h
  exact h

theorem single_factor_bounds [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v})
    (hp : p.Prime) (ho : Odd p) (hf : Function.Injective σ) :
    2 ≤ Module.finrank (ZMod 2) W ∧
    (p ≠ 3 → 4 ≤ Module.finrank (ZMod 2) W) ∧
    (5 < p → 4 < Module.finrank (ZMod 2) W) := by
  obtain ⟨hd, hm, hpos⟩ := split_dimensions σ split hp ho hf
  have hmod := rotationMoved_card_modEq σ hp (split W p hp ho σ hf).1.disjoint
  rw [hm] at hmod
  have hsmall (h : Module.finrank (ZMod 2) (reflectionHalf σ) = 1) : p = 3 := by
    rw [h] at hmod
    norm_num at hmod
    have hdiv : p ∣ 3 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 4)).mp hmod.symm
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv).resolve_left hp.ne_one
  refine ⟨by omega, ?_, ?_⟩
  · intro hp3
    have : Module.finrank (ZMod 2) (reflectionHalf σ) ≠ 1 := fun h => hp3 (hsmall h)
    omega
  · intro hp5
    by_contra h
    have hw : Module.finrank (ZMod 2) (reflectionHalf σ) ≤ 2 := by omega
    have hw2 : Module.finrank (ZMod 2) (reflectionHalf σ) = 2 := by
      have : Module.finrank (ZMod 2) (reflectionHalf σ) ≠ 1 := by
        intro he
        have := hsmall he
        omega
      omega
    rw [hw2] at hmod
    norm_num at hmod
    have hdiv : p ∣ 15 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 16)).mp hmod.symm
    have hh : p ∣ 3 ∨ p ∣ 5 := hp.dvd_mul.mp hdiv
    rcases hh with hh | hh
    · have := Nat.le_of_dvd (by decide : 0 < 3) hh; omega
    · have := Nat.le_of_dvd (by decide : 0 < 5) hh; omega

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree
