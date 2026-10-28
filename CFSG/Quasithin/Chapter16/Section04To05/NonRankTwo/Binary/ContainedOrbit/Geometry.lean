module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.ContainedOrbit.Basic
public import Theory.SpecificGroups.OrthogonalFourBinary.NonsingularSix
public import Mathlib.Data.Set.Card

/-!
# Two nonsingular slices in the actual local action

Coordinates compatible with the full orthogonal action give two disjoint
six-element stabilizer orbits in A, distinguished by the central coordinate.
Either orbit together with z generates A: every four-space vector is a sum
of two nonsingular vectors. The Δ₀ exclusion places every nontrivial
normalizer conjugate of z in one of these slices.

The marked coordinates remain an explicit construction obligation. These
are conditional deductions from `LocalAction`, not a completion of 16.5.12.
Source: Aschbacher–Smith, combined manuscript, printed pp.1200–1201.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary.ContainedOrbit

open Subgroup MulAction OrthogonalFourBinary Theory.AlgebraicGroup

variable {G : Type*} [Group G] {L A : Subgroup G} {z : A}

/-- One of the two six-point slices, with the indicated central coordinate. -/
def LocalAction.slice (d : LocalAction L A z) (ε : F) : Set A :=
  {a | form (Multiplicative.toAdd (d.coordinates a).1) = 1 ∧
    (d.coordinates a).2 = Multiplicative.ofAdd ε}

private def LocalAction.sliceEquiv (d : LocalAction L A z) (ε : F) :
    d.slice ε ≃ {v : Space // form v = 1} where
  toFun a := ⟨Multiplicative.toAdd (d.coordinates a.val).1, a.property.1⟩
  invFun v := ⟨d.coordinates.symm (Multiplicative.ofAdd v.val, Multiplicative.ofAdd ε),
    by simp [LocalAction.slice, v.property]⟩
  left_inv a := by
    apply Subtype.ext
    apply d.coordinates.injective
    simp only [MulEquiv.apply_symm_apply]
    exact Prod.ext rfl a.property.2.symm
  right_inv v := by simp

theorem LocalAction.slice_card (d : LocalAction L A z) (ε : F) :
    Nat.card (d.slice ε) = 6 :=
  (Nat.card_congr (d.sliceEquiv ε)).trans nonsingular_card

theorem LocalAction.central_not_mem_slice (d : LocalAction L A z) (ε : F) :
    z ∉ d.slice ε := by
  intro hz
  have hh := hz.1
  rw [d.central_coordinate] at hh
  have he : form (Multiplicative.toAdd centralVector.1) = 0 := by decide +kernel
  rw [he] at hh
  exact zero_ne_one hh

theorem LocalAction.slices_disjoint (d : LocalAction L A z) :
    Disjoint (d.slice 0) (d.slice 1) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have he := hx.2.symm.trans hy.2
  exact (by decide : (Multiplicative.ofAdd (0 : F)) ≠ Multiplicative.ofAdd 1) he

/-- Each slice is precisely an orbit of the actual stabilizer in M⁺. -/
theorem LocalAction.orbit_eq_slice (d : LocalAction L A z) {ε : F}
    {a : A} (ha : a ∈ d.slice ε) :
    orbit (stabilizer (normalizerImage A) z) a = d.slice ε := by
  ext b
  constructor
  · rintro ⟨m, rfl⟩
    change form (Multiplicative.toAdd (d.coordinates (m • a)).1) = 1 ∧
      (d.coordinates (m • a)).2 = Multiplicative.ofAdd ε
    rw [d.intertwines]
    exact ⟨((mem_quadraticIsometrySubgroup form _).mp (d.actor m).property _).trans ha.1,
      ha.2⟩
  · intro hb
    obtain ⟨e, he⟩ := exists_isometry_of_nonsingular
      (Multiplicative.toAdd (d.coordinates a).1)
      (Multiplicative.toAdd (d.coordinates b).1) ha.1 hb.1
    refine ⟨d.actor.symm e, d.coordinates.injective ?_⟩
    rw [d.intertwines, d.actor.apply_symm_apply]
    exact Prod.ext (congrArg Multiplicative.ofAdd he) (ha.2.trans hb.2.symm)

/-- The order computation concerns the stabilizer in the genuine conjugation image. -/
theorem LocalAction.stabilizer_card (d : LocalAction L A z) :
    Nat.card (stabilizer (normalizerImage A) z) = 72 :=
  (Nat.card_congr d.actor.toEquiv).trans isometryGroup_card

/-- Either nonsingular slice together with z generates the whole elementary group. -/
theorem LocalAction.slice_generates (d : LocalAction L A z) (ε : F) :
    closure (insert z (d.slice ε)) = ⊤ := by
  let P := closure (insert z (d.slice ε))
  have hz : z ∈ P := subset_closure (Set.mem_insert _ _)
  have hc (c : F) : d.coordinates.symm (1, Multiplicative.ofAdd c) ∈ P := by
    have cases : c = 0 ∨ c = 1 := (by decide : ∀ c : F, c = 0 ∨ c = 1) c
    rcases cases with rfl | rfl
    · change d.coordinates.symm 1 ∈ P
      rw [map_one]
      exact P.one_mem
    · have he : d.coordinates.symm (1, Multiplicative.ofAdd (1 : F)) = z :=
        d.coordinates.symm_apply_eq.mpr d.central_coordinate.symm
      rwa [he]
  have hs (v : Space) (hv : form v = 1) :
      d.coordinates.symm (Multiplicative.ofAdd v, Multiplicative.ofAdd ε) ∈ P := by
    apply Subgroup.subset_closure
    right
    simp [LocalAction.slice, hv]
  apply top_unique
  intro x _
  obtain ⟨a, b, ha, hb, he⟩ :=
    sum_two_nonsingular (Multiplicative.toAdd (d.coordinates x).1)
  have hm := P.mul_mem (P.mul_mem (hs a ha) (hs b hb))
    (hc (Multiplicative.toAdd (d.coordinates x).2))
  have hid : ∀ (a b : Space) (ε c : F),
      (Multiplicative.ofAdd a, Multiplicative.ofAdd ε) *
        (Multiplicative.ofAdd b, Multiplicative.ofAdd ε) *
          (1, Multiplicative.ofAdd c) =
      (Multiplicative.ofAdd (a + b), Multiplicative.ofAdd c) := by decide +kernel
  rw [← map_mul, ← map_mul, hid, ← he] at hm
  simpa using hm

/-- Two-central exclusion leaves only the two nonsingular slices away from z. -/
theorem LocalAction.mem_slices_of_not_twoCentralProjection (d : LocalAction L A z)
    {x : A} (hx1 : x ≠ 1) (hxz : x ≠ z)
    (hx : ¬ HasTwoCentralProjection L (x : G)) :
    x ∈ d.slice 0 ∪ d.slice 1 := by
  have hfirst : (d.coordinates x).1 ≠ 1 := by
    intro h0
    have cases : (d.coordinates x).2 = 1 ∨
        (d.coordinates x).2 = Multiplicative.ofAdd (1 : F) :=
      (by decide : ∀ c : Multiplicative F, c = 1 ∨ c = Multiplicative.ofAdd (1 : F)) _
    rcases cases with h | h
    · apply hx1
      apply d.coordinates.injective
      rw [map_one]
      exact Prod.ext h0 h
    · exact hxz (d.coordinates.injective ((Prod.ext h0 h).trans d.central_coordinate.symm))
  have hq : form (Multiplicative.toAdd (d.coordinates x).1) = 1 := by
    have hn : form (Multiplicative.toAdd (d.coordinates x).1) ≠ 0 :=
      fun hh => hx ((d.singular_projection x hfirst).mp hh)
    exact (by decide : ∀ c : F, c ≠ 0 → c = 1) _ hn
  have cases : (d.coordinates x).2 = Multiplicative.ofAdd (0 : F) ∨
      (d.coordinates x).2 = Multiplicative.ofAdd (1 : F) :=
    (by decide : ∀ c : Multiplicative F,
      c = Multiplicative.ofAdd (0 : F) ∨ c = Multiplicative.ofAdd (1 : F)) _
  exact cases.elim (fun h => Or.inl ⟨hq, h⟩) (fun h => Or.inr ⟨hq, h⟩)

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary.ContainedOrbit
