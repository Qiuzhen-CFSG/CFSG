module

public import CFSG.Quasithin.ChapterE.Section06.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# The odd Cartan parameter in E.6.27

Definition E.3.37 takes the largest exponent `c` for which the finite group
contains a cyclic group of order `2^c - 1` inside an abelian odd-order subgroup
permuting with one of its own Sylow two-subgroups. In particular the Sylow
subgroup belongs to the group whose parameter is measured, even when that
group is itself an automizer subgroup.

The order bound makes the supremum a genuine maximum. A surjective map
preserves a witness if it is injective on the cyclic subgroup; injectivity on
the whole odd overgroup is unnecessary. This is the faithful Cartan step of
Proposition E.6.27, with the Cartan subgroup's construction kept separate.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Definition
E.3.37 and Proposition E.6.27, printed pp.239 and 257 (PDF pp.250 and 268).
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

universe u v
variable {X : Type u} [Group X] [Finite X]
variable {Y : Type v} [Group Y] [Finite Y]

/-- The complete witness in E.3.37, intrinsic to `X`. -/
structure NPrimeWitness (X : Type u) [Group X] (c : ℕ) : Type u where
  abelianGroup : Subgroup X
  cyclicGroup : Subgroup X
  sylow : Sylow 2 X
  cyclic_le : cyclicGroup ≤ abelianGroup
  abelian : IsMulCommutative abelianGroup
  odd : Odd (Nat.card abelianGroup)
  cyclic : IsCyclic cyclicGroup
  card : Nat.card cyclicGroup = 2 ^ c - 1
  permutes : (abelianGroup : Set X) * (sylow : Set X) =
    (sylow : Set X) * (abelianGroup : Set X)

/-- Definition E.3.37, applied to a finite group rather than an ambient tag. -/
noncomputable def nPrime (X : Type u) [Group X] [Finite X] : ℕ :=
  sSup {c : ℕ | Nonempty (NPrimeWitness X c)}

theorem NPrimeWitness.exponent_le_card {c : ℕ} (w : NPrimeWitness X c) :
    c ≤ Nat.card X := by
  have hpow : c + 1 ≤ 2 ^ c := c.lt_two_pow_self
  have hcard : 2 ^ c - 1 ≤ Nat.card X :=
    w.card ▸ card_le_card_group w.cyclicGroup
  omega

theorem nPrimeWitness_bddAbove :
    BddAbove {c : ℕ | Nonempty (NPrimeWitness X c)} := by
  exact ⟨Nat.card X, fun c ⟨w⟩ => w.exponent_le_card⟩

theorem NPrimeWitness.le_nPrime {c : ℕ} (w : NPrimeWitness X c) :
    c ≤ nPrime X :=
  le_csSup nPrimeWitness_bddAbove ⟨w⟩

/-- The trivial cyclic group supplies exponent one, including for odd groups. -/
noncomputable def trivialWitness (X : Type u) [Group X] : NPrimeWitness X 1 where
  abelianGroup := ⊥
  cyclicGroup := ⊥
  sylow := Classical.choice Sylow.nonempty
  cyclic_le := le_rfl
  abelian := inferInstance
  odd := by simp
  cyclic := inferInstance
  card := by simp
  permutes := by simp

theorem one_le_nPrime : 1 ≤ nPrime X := (trivialWitness X).le_nPrime

/-- The supremum defining `nPrime` is attained. -/
theorem nPrime_spec : Nonempty (NPrimeWitness X (nPrime X)) := by
  exact Nat.sSup_mem (s := {c : ℕ | Nonempty (NPrimeWitness X c)})
    ⟨1, ⟨trivialWitness X⟩⟩ nPrimeWitness_bddAbove

theorem nPrime_le_iff {j : ℕ} :
    nPrime X ≤ j ↔ ∀ c, NPrimeWitness X c → c ≤ j := by
  constructor
  · exact fun h _ w => w.le_nPrime.trans h
  · intro h
    obtain ⟨w⟩ := nPrime_spec (X := X)
    exact h _ w

/-- Quotient transport retains the entire E.3.37 witness. -/
noncomputable def NPrimeWitness.map {c : ℕ} (w : NPrimeWitness X c)
    (f : X →* Y) (hf : Function.Surjective f)
    (hcyclic : Function.Injective (f.comp w.cyclicGroup.subtype)) :
    NPrimeWitness Y c := by
  letI := w.abelian
  letI := w.cyclic
  refine {
    abelianGroup := w.abelianGroup.map f
    cyclicGroup := w.cyclicGroup.map f
    sylow := w.sylow.mapSurjective hf
    cyclic_le := map_mono w.cyclic_le
    abelian := inferInstance
    odd := w.odd.of_dvd_nat (card_map_dvd _ _)
    cyclic := ?_
    card := ?_
    permutes := ?_
  }
  · exact isCyclic_of_surjective (f.subgroupMap w.cyclicGroup)
      (f.subgroupMap_surjective _)
  · have hr : (f.comp w.cyclicGroup.subtype).range = w.cyclicGroup.map f := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hcyclic).toEquiv]
    exact w.card
  · change (f '' (w.abelianGroup : Set X)) * (f '' (w.sylow : Set X)) =
      (f '' (w.sylow : Set X)) * (f '' (w.abelianGroup : Set X))
    rw [← Set.image_mul, ← Set.image_mul, w.permutes]

theorem nPrime_eq_of_mulEquiv (e : X ≃* Y) : nPrime X = nPrime Y := by
  apply Nat.le_antisymm
  · obtain ⟨w⟩ := nPrime_spec (X := X)
    exact (w.map e.toMonoidHom e.surjective
      (e.injective.comp w.cyclicGroup.subtype_injective)).le_nPrime
  · obtain ⟨w⟩ := nPrime_spec (X := Y)
    exact (w.map e.symm.toMonoidHom e.symm.surjective
      (e.symm.injective.comp w.cyclicGroup.subtype_injective)).le_nPrime

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

end
