module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Marked

/-!
# Diagonal lifts and their Borel complements

A `DiagonalSection` is an actual homomorphism Fˣ → L lifting each diagonal
matrix under the marked quotient map. Its range is cyclic of order |F|−1.
The root/diagonal factorization downstairs and the root-preimage description
of the given Sylow subgroup prove B = SX and S ∩ X = 1 upstairs.

Existence of the section is not assumed as a block property and is not proved
here. It is the separate Schur–Zassenhaus lifting obligation. This interface
lets that construction and the center-module calculation proceed independently.

Source: Aschbacher–Smith, the first step of the L₂ case of E.6.7,
printed p.246. No covering-module conclusion is part of `DiagonalSection`.
-/

@[expose] public section

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {L : Type*} [Group L] {F : Type*} [Field F] {B : Subgroup L}

structure DiagonalSection (a : MarkedBlockModel L B F) where
  lift : Fˣ →* L
  quotient_eq : ∀ u : Fˣ, a.linearMap (lift u) = diag2 (u : F) u.ne_zero

variable {a : MarkedBlockModel L B F}

def DiagonalSection.torus (d : DiagonalSection a) : Subgroup L := d.lift.range

theorem DiagonalSection.injective (d : DiagonalSection a) : Function.Injective d.lift := by
  intro u v h
  have hh := congrArg a.linearMap h
  rw [d.quotient_eq, d.quotient_eq] at hh
  apply Units.ext
  simpa [diag2_coe'] using congrArg (fun g : SL(2, F) => g.val 0 0) hh

noncomputable def DiagonalSection.torusEquiv (d : DiagonalSection a) : d.torus ≃* Fˣ :=
  (MonoidHom.ofInjective d.injective).symm

theorem DiagonalSection.lift_torusEquiv (d : DiagonalSection a) (x : d.torus) :
    d.lift (d.torusEquiv x) = (x : L) :=
  congrArg Subtype.val ((MonoidHom.ofInjective d.injective).apply_symm_apply x)

theorem DiagonalSection.quotient_torusEquiv (d : DiagonalSection a) (x : d.torus) :
    a.linearMap (x : L) = diag2 (d.torusEquiv x : F) (d.torusEquiv x).ne_zero := by
  rw [← d.lift_torusEquiv x, d.quotient_eq]

theorem DiagonalSection.torus_cyclic [Finite F] (d : DiagonalSection a) : IsCyclic d.torus :=
  isCyclic_of_injective d.torusEquiv.toMonoidHom d.torusEquiv.injective

theorem DiagonalSection.torus_card [Finite F] (d : DiagonalSection a) :
    Nat.card d.torus = Nat.card F - 1 := by
  rw [Nat.card_congr d.torusEquiv.toEquiv, Nat.card_units]

theorem DiagonalSection.torus_le_borel (d : DiagonalSection a) : d.torus ≤ B := by
  rintro x ⟨u, rfl⟩
  apply le_of_eq a.borel.symm
  change a.linearMap (d.lift u) ∈ rankOneBorel F
  rw [d.quotient_eq]
  exact diag_mem_rankOneBorel (u : F) u.ne_zero

theorem DiagonalSection.normalizes_sylow [Finite F] [CharP F 2]
    (d : DiagonalSection a) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    d.torus ≤ normalizer (S : Set L) :=
  d.torus_le_borel.trans (a.borel_normalizes_sylow S hS)

theorem DiagonalSection.disjoint_sylow [Finite F] [CharP F 2]
    (d : DiagonalSection a) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    Disjoint (S : Subgroup L) d.torus := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxS, u, rfl⟩
  rw [a.sylow_eq_root_comap S hS] at hxS
  obtain ⟨t, ht⟩ := (mem_upperUnipotent F _).mp hxS
  rw [d.quotient_eq] at ht
  have hu : u = 1 := by
    apply Units.ext
    simpa [diag2_coe', transvection_coe] using
      (congrArg (fun g : SL(2, F) => g.val 0 0) ht).symm
  simp [hu]

theorem DiagonalSection.borel_product [Finite F] [CharP F 2]
    (d : DiagonalSection a) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    (B : Set L) = (S : Set L) * (d.torus : Set L) := by
  ext g
  constructor
  · intro hg
    have hf : a.linearMap g ∈ rankOneBorel F := le_of_eq a.borel hg
    obtain ⟨t, u, hu, he⟩ := rankOneBorel_factor ⟨a.linearMap g, hf⟩
    change a.linearMap g = transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t *
      diag2 u hu at he
    let v : Fˣ := Units.mk0 u hu
    have hs : g * (d.lift v)⁻¹ ∈ (S : Subgroup L) := by
      rw [a.sylow_eq_root_comap S hS]
      change a.linearMap (g * (d.lift v)⁻¹) ∈ upperUnipotent F
      rw [map_mul, map_inv, d.quotient_eq]
      change a.linearMap g * (diag2 u hu)⁻¹ ∈ upperUnipotent F
      rw [he, mul_inv_cancel_right]
      exact (mem_upperUnipotent F _).mpr ⟨t, rfl⟩
    exact ⟨g * (d.lift v)⁻¹, hs, d.lift v, ⟨v, rfl⟩, inv_mul_cancel_right _ _⟩
  · rintro ⟨s, hs, x, hx, rfl⟩
    exact B.mul_mem (hS hs) (d.torus_le_borel hx)

end CFSG.Quasithin.ChapterE.Section06.L2Torus
