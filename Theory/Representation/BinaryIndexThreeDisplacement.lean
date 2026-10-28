module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Set.Card

/-!
# Binary displacement at an index-three stabilizer

A vector fixed by an index-three subgroup has either one or three orbit
points. If a normal supplement moves it, its orbit consists of all three
points. The two nonzero differences from the original vector are distinct,
so they span a binary plane and give a commutator subspace of order four.

This supplies the second moved-image calculation in Aschbacher--Smith,
Lemma 14.4.12, printed pp.1011--1012, without prescribing the full action
image of the residual on a larger module.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A moving normal supplement of an index-three point stabilizer moves a
binary line through precisely a plane. No faithfulness assumption is needed. -/
theorem index_three_displacement_card (ρ : Representation (ZMod 2) G V)
    (S A : Subgroup G) [A.Normal] (hgen : A ⊔ S = ⊤) (hi : S.index = 3)
    (v : V) (hfix : ∀ s ∈ S, ρ s v = v) (hmove : ∃ a ∈ A, ρ a v ≠ v) :
    Nat.card (subspaceCommutator ρ (Submodule.span (ZMod 2) {v}) A) = 4 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : MulAction G V := {
    smul := fun g w => ρ g w
    one_smul := by intro w; change ρ 1 w = w; simp
    mul_smul := by intro g h w; change ρ (g * h) w = ρ g (ρ h w); simp }
  have hSK : S ≤ MulAction.stabilizer G v := hfix
  have hki : (MulAction.stabilizer G v).index = 3 := by
    have hd : (MulAction.stabilizer G v).index ∣ 3 := hi ▸ index_dvd_of_le hSK
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · have hk := index_eq_one.mp h
      obtain ⟨a, ha, hm⟩ := hmove
      exact (hm (show a ∈ MulAction.stabilizer G v from hk ▸ mem_top a)).elim
    · exact h
  have horbit : (MulAction.orbit G v).ncard = 3 := by
    rw [← MulAction.index_stabilizer G v]
    exact hki
  have hvO : v ∈ MulAction.orbit G v := MulAction.mem_orbit_self v
  have htwo : (MulAction.orbit G v \ {v}).ncard = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem hvO, horbit]
  obtain ⟨w, z, hwz, hO⟩ := Set.ncard_eq_two.mp htwo
  have hw : w ∈ MulAction.orbit G v ∧ w ≠ v := by
    have : w ∈ MulAction.orbit G v \ {v} := by rw [hO]; simp
    simpa using this
  have hz : z ∈ MulAction.orbit G v ∧ z ≠ v := by
    have : z ∈ MulAction.orbit G v \ {v} := by rw [hO]; simp
    simpa using this
  have haO : ∀ y ∈ MulAction.orbit G v, ∃ a ∈ A, ρ a v = y := by
    intro y hy
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    have hg : g ∈ A ⊔ S := hgen ▸ mem_top g
    obtain ⟨a, ha, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨a, ha, ?_⟩
    change ρ a v = ρ (a * s) v
    rw [map_mul, Module.End.mul_apply, hfix s hs]
  let D := subspaceCommutator ρ (Submodule.span (ZMod 2) {v}) A
  have hdw : w - v ∈ D := by
    obtain ⟨a, ha, rfl⟩ := haO w hw.1
    exact Submodule.subset_span ⟨a, ha, v, Submodule.mem_span_singleton_self v, rfl⟩
  have hdz : z - v ∈ D := by
    obtain ⟨a, ha, rfl⟩ := haO z hz.1
    exact Submodule.subset_span ⟨a, ha, v, Submodule.mem_span_singleton_self v, rfl⟩
  have hspan : D = Submodule.span (ZMod 2) {w - v, z - v} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, u, hu, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [map_smul, ← smul_sub]
      apply Submodule.smul_mem
      by_cases he : ρ a v = v
      · rw [he, sub_self]; exact Submodule.zero_mem _
      · have hmem : ρ a v ∈ MulAction.orbit G v \ {v} :=
          ⟨MulAction.mem_orbit_iff.mpr ⟨a, rfl⟩, he⟩
        rw [hO] at hmem
        rcases hmem with h | h
        · rw [h]; exact Submodule.subset_span (Set.mem_insert _ _)
        · rw [show ρ a v = z from h]; exact Submodule.subset_span (by simp)
    · apply Submodule.span_le.mpr
      intro u hu
      rcases hu with rfl | hu
      · exact hdw
      · exact (show u = z - v from hu) ▸ hdz
  have hupper : Module.finrank (ZMod 2) D ≤ 2 := by
    rw [hspan]
    have he : (({w-v,z-v} : Finset V) : Set V) = {w-v,z-v} := by ext; simp
    have h := finrank_span_finset_le_card (R := ZMod 2) ({w-v,z-v} : Finset V)
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (({w-v,z-v} : Finset V) : Set V)) ≤ _ at h
    rw [he] at h
    exact h.trans (by simp [hwz])
  let f : Fin 3 → D := ![0, ⟨w-v,hdw⟩, ⟨z-v,hdz⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hh := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      simp [f, sub_ne_zero.mpr hw.2, sub_ne_zero.mpr hz.2, hwz,
        Ne.symm (sub_ne_zero.mpr hw.2), Ne.symm (sub_ne_zero.mpr hz.2), Ne.symm hwz] at hh ⊢
  have hlower := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hlower
  have hdim : Module.finrank (ZMod 2) D = 2 := by
    interval_cases h : Module.finrank (ZMod 2) D <;> simp_all
  change Nat.card D = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
  rfl

end Representation.BinaryOffender
