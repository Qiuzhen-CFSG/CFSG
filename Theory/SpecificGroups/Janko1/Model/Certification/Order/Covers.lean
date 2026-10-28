module

public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.InnerEdges
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterEdges0
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterEdges40
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterEdges80
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterEdges120
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterEdges160
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterEdges200
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterEdges240

/-!
# The two finite coset covers for the J₁ order certificate

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Positive transitions suffice in a finite group: the inverse of a generator
is itself a nonnegative power of that generator. -/
private noncomputable def positiveCover {G α ι : Type*} [Group G] [Finite G]
    (K : Subgroup G) (g : α → G) (r : ι → G) (i₀ : ι) (h₀ : r i₀ = 1)
    (step : ∀ i a, ∃ h : K, ∃ j, r i * g a = h.val * r j) :
    Subgroup.GeneratorCosetCover K g ι where
  repr := r
  initial := i₀
  initial_eq := h₀
  step := step
  inv_step := by
    intro i a
    have hp : ∀ n : ℕ, ∀ i, ∃ h : K, ∃ j, r i * g a ^ n = h.val * r j := by
      intro n
      induction n with
      | zero => intro i; exact ⟨1, i, by simp⟩
      | succ n ih =>
        intro i
        obtain ⟨h, j, he⟩ := ih i
        obtain ⟨h', k, he'⟩ := step j a
        refine ⟨h * h', k, ?_⟩
        simp only [pow_succ, ← mul_assoc, he, Subgroup.coe_mul]
        rw [mul_assoc, he', ← mul_assoc]
    have hi : (g a)⁻¹ ∈ Submonoid.powers (g a) :=
      mem_powers_iff_mem_zpowers.mpr ((Subgroup.zpowers (g a)).inv_mem (Subgroup.mem_zpowers (g a)))
    obtain ⟨n, hn⟩ := hi
    rw [← hn]
    exact hp n i

@[expose] public def innerGenerators (t : Bool) : H := if t then hy else hx
@[expose] public def outerGenerators (t : Bool) : Model := if t then b else a

public theorem inner_generates : Subgroup.closure (Set.range innerGenerators) = ⊤ := by
  have hs : Set.range innerGenerators = Subtype.val ⁻¹' ({x, y} : Set Model) := by
    ext q
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, rfl⟩
      cases t <;> simp [innerGenerators, hx, hy]
    · rintro (he | he)
      · refine ⟨false, ?_⟩
        apply Subtype.ext
        exact he.symm
      · refine ⟨true, ?_⟩
        apply Subtype.ext
        exact he.symm
  rw [hs]
  exact Subgroup.closure_closure_coe_preimage

public theorem outer_generates : Subgroup.closure (Set.range outerGenerators) = ⊤ := by
  have hs : Set.range outerGenerators = ({a, b} : Set Model) := by
    ext q
    simp [outerGenerators]
  rw [hs]
  exact closure_pair_eq_top

public noncomputable def innerCover :
    Subgroup.GeneratorCosetCover (Subgroup.zpowers hz) innerGenerators (Fin 60) :=
  positiveCover _ _ innerReps 0 rfl (by
    intro i t
    fin_cases i
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 1, innerEdge0_0⟩
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 1, innerEdge0_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 2, innerEdge1_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 3, innerEdge1_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 4, innerEdge2_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 5, innerEdge2_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 6, innerEdge3_0⟩
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 0, innerEdge3_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 7, innerEdge4_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 8, innerEdge4_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 9, innerEdge5_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 10, innerEdge5_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 11, innerEdge6_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 12, innerEdge6_1⟩
    · cases t
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 10, innerEdge7_0⟩
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 11, innerEdge7_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 13, innerEdge8_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 14, innerEdge8_1⟩
    · cases t
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 8, innerEdge9_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 15, innerEdge9_1⟩
    · cases t
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 0, innerEdge10_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 2, innerEdge10_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 16, innerEdge11_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 17, innerEdge11_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 18, innerEdge12_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 19, innerEdge12_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 17, innerEdge13_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 20, innerEdge13_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 21, innerEdge14_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 4, innerEdge14_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 22, innerEdge15_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 23, innerEdge15_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 14, innerEdge16_0⟩
      · exact ⟨⟨hz ^ 6, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 6⟩, 18, innerEdge16_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 24, innerEdge17_0⟩
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 7, innerEdge17_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 25, innerEdge18_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 26, innerEdge18_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 27, innerEdge19_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 6, innerEdge19_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 28, innerEdge20_0⟩
      · exact ⟨⟨hz ^ 2, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 2⟩, 28, innerEdge20_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 3, innerEdge21_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 29, innerEdge21_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 30, innerEdge22_0⟩
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 24, innerEdge22_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 31, innerEdge23_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 9, innerEdge23_1⟩
    · cases t
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 5, innerEdge24_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 32, innerEdge24_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 33, innerEdge25_0⟩
      · exact ⟨⟨hz ^ 6, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 6⟩, 33, innerEdge25_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 34, innerEdge26_0⟩
      · exact ⟨⟨hz ^ 5, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 5⟩, 16, innerEdge26_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 29, innerEdge27_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 35, innerEdge27_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 36, innerEdge28_0⟩
      · exact ⟨⟨hz ^ 9, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 9⟩, 13, innerEdge28_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 37, innerEdge29_0⟩
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 34, innerEdge29_1⟩
    · cases t
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 20, innerEdge30_0⟩
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 36, innerEdge30_1⟩
    · cases t
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 32, innerEdge31_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 38, innerEdge31_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 39, innerEdge32_0⟩
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 22, innerEdge32_1⟩
    · cases t
      · exact ⟨⟨hz ^ 6, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 6⟩, 26, innerEdge33_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 40, innerEdge33_1⟩
    · cases t
      · exact ⟨⟨hz ^ 5, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 5⟩, 12, innerEdge34_0⟩
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 21, innerEdge34_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 41, innerEdge35_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 42, innerEdge35_1⟩
    · cases t
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 15, innerEdge36_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 43, innerEdge36_1⟩
    · cases t
      · exact ⟨⟨hz ^ 6, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 6⟩, 40, innerEdge37_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 44, innerEdge37_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 45, innerEdge38_0⟩
      · exact ⟨⟨hz ^ 7, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 7⟩, 45, innerEdge38_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 43, innerEdge39_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 46, innerEdge39_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 47, innerEdge40_0⟩
      · exact ⟨⟨hz ^ 5, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 5⟩, 25, innerEdge40_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 48, innerEdge41_0⟩
      · exact ⟨⟨hz ^ 8, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 8⟩, 48, innerEdge41_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 49, innerEdge42_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 27, innerEdge42_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 50, innerEdge43_0⟩
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 30, innerEdge43_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 51, innerEdge44_0⟩
      · exact ⟨⟨hz ^ 8, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 8⟩, 49, innerEdge44_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 52, innerEdge45_0⟩
      · exact ⟨⟨hz ^ 4, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 4⟩, 31, innerEdge45_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 53, innerEdge46_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 54, innerEdge46_1⟩
    · cases t
      · exact ⟨⟨hz ^ 5, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 5⟩, 19, innerEdge47_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 55, innerEdge47_1⟩
    · cases t
      · exact ⟨⟨hz ^ 8, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 8⟩, 42, innerEdge48_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 56, innerEdge48_1⟩
    · cases t
      · exact ⟨⟨hz ^ 6, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 6⟩, 55, innerEdge49_0⟩
      · exact ⟨⟨hz ^ 3, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 3⟩, 37, innerEdge49_1⟩
    · cases t
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 23, innerEdge50_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 57, innerEdge50_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 56, innerEdge51_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 50, innerEdge51_1⟩
    · cases t
      · exact ⟨⟨hz ^ 3, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 3⟩, 57, innerEdge52_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 58, innerEdge52_1⟩
    · cases t
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 58, innerEdge53_0⟩
      · exact ⟨⟨hz ^ 6, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 6⟩, 47, innerEdge53_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 59, innerEdge54_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 39, innerEdge54_1⟩
    · cases t
      · exact ⟨⟨hz ^ 8, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 8⟩, 35, innerEdge55_0⟩
      · exact ⟨⟨hz ^ 5, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 5⟩, 53, innerEdge55_1⟩
    · cases t
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 46, innerEdge56_0⟩
      · exact ⟨⟨hz ^ 3, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 3⟩, 41, innerEdge56_1⟩
    · cases t
      · exact ⟨⟨hz ^ 7, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 7⟩, 54, innerEdge57_0⟩
      · exact ⟨⟨hz ^ 0, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 0⟩, 51, innerEdge57_1⟩
    · cases t
      · exact ⟨⟨hz ^ 10, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 10⟩, 44, innerEdge58_0⟩
      · exact ⟨⟨hz ^ 6, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 6⟩, 59, innerEdge58_1⟩
    · cases t
      · exact ⟨⟨hz ^ 1, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 1⟩, 38, innerEdge59_0⟩
      · exact ⟨⟨hz ^ 5, (Subgroup.zpowers hz).pow_mem (Subgroup.mem_zpowers hz) 5⟩, 52, innerEdge59_1⟩)

public noncomputable def outerCover :
    Subgroup.GeneratorCosetCover H outerGenerators (Fin 266) :=
  positiveCover _ _ outerReps 0 rfl (by
    intro i t
    fin_cases i
    · cases t
      · exact ⟨factor5_39, 0, outerEdge0_0⟩
      · exact ⟨factor0_0, 1, outerEdge0_1⟩
    · cases t
      · exact ⟨factor0_0, 2, outerEdge1_0⟩
      · exact ⟨factor0_0, 3, outerEdge1_1⟩
    · cases t
      · exact ⟨factor0_0, 1, outerEdge2_0⟩
      · exact ⟨factor0_0, 4, outerEdge2_1⟩
    · cases t
      · exact ⟨factor0_0, 5, outerEdge3_0⟩
      · exact ⟨factor0_0, 0, outerEdge3_1⟩
    · cases t
      · exact ⟨factor0_0, 6, outerEdge4_0⟩
      · exact ⟨factor0_0, 7, outerEdge4_1⟩
    · cases t
      · exact ⟨factor0_0, 3, outerEdge5_0⟩
      · exact ⟨factor0_0, 8, outerEdge5_1⟩
    · cases t
      · exact ⟨factor0_0, 4, outerEdge6_0⟩
      · exact ⟨factor0_0, 9, outerEdge6_1⟩
    · cases t
      · exact ⟨factor0_0, 10, outerEdge7_0⟩
      · exact ⟨factor0_0, 2, outerEdge7_1⟩
    · cases t
      · exact ⟨factor0_0, 11, outerEdge8_0⟩
      · exact ⟨factor0_0, 12, outerEdge8_1⟩
    · cases t
      · exact ⟨factor0_0, 13, outerEdge9_0⟩
      · exact ⟨factor0_0, 14, outerEdge9_1⟩
    · cases t
      · exact ⟨factor0_0, 7, outerEdge10_0⟩
      · exact ⟨factor0_0, 15, outerEdge10_1⟩
    · cases t
      · exact ⟨factor0_0, 8, outerEdge11_0⟩
      · exact ⟨factor0_0, 16, outerEdge11_1⟩
    · cases t
      · exact ⟨factor0_0, 17, outerEdge12_0⟩
      · exact ⟨factor0_0, 5, outerEdge12_1⟩
    · cases t
      · exact ⟨factor0_0, 9, outerEdge13_0⟩
      · exact ⟨factor0_0, 18, outerEdge13_1⟩
    · cases t
      · exact ⟨factor0_0, 19, outerEdge14_0⟩
      · exact ⟨factor0_0, 6, outerEdge14_1⟩
    · cases t
      · exact ⟨factor0_0, 20, outerEdge15_0⟩
      · exact ⟨factor0_0, 21, outerEdge15_1⟩
    · cases t
      · exact ⟨factor0_0, 22, outerEdge16_0⟩
      · exact ⟨factor0_0, 23, outerEdge16_1⟩
    · cases t
      · exact ⟨factor0_0, 12, outerEdge17_0⟩
      · exact ⟨factor0_0, 24, outerEdge17_1⟩
    · cases t
      · exact ⟨factor0_0, 25, outerEdge18_0⟩
      · exact ⟨factor0_0, 26, outerEdge18_1⟩
    · cases t
      · exact ⟨factor0_0, 14, outerEdge19_0⟩
      · exact ⟨factor0_0, 27, outerEdge19_1⟩
    · cases t
      · exact ⟨factor0_0, 15, outerEdge20_0⟩
      · exact ⟨factor0_0, 28, outerEdge20_1⟩
    · cases t
      · exact ⟨factor0_0, 29, outerEdge21_0⟩
      · exact ⟨factor0_0, 10, outerEdge21_1⟩
    · cases t
      · exact ⟨factor0_0, 16, outerEdge22_0⟩
      · exact ⟨factor0_0, 30, outerEdge22_1⟩
    · cases t
      · exact ⟨factor0_0, 31, outerEdge23_0⟩
      · exact ⟨factor0_0, 11, outerEdge23_1⟩
    · cases t
      · exact ⟨factor0_0, 32, outerEdge24_0⟩
      · exact ⟨factor5_39, 25, outerEdge24_1⟩
    · cases t
      · exact ⟨factor0_0, 18, outerEdge25_0⟩
      · exact ⟨factor5_39, 17, outerEdge25_1⟩
    · cases t
      · exact ⟨factor0_0, 33, outerEdge26_0⟩
      · exact ⟨factor0_0, 13, outerEdge26_1⟩
    · cases t
      · exact ⟨factor0_0, 34, outerEdge27_0⟩
      · exact ⟨factor0_0, 35, outerEdge27_1⟩
    · cases t
      · exact ⟨factor5_43, 28, outerEdge28_0⟩
      · exact ⟨factor0_0, 36, outerEdge28_1⟩
    · cases t
      · exact ⟨factor0_0, 21, outerEdge29_0⟩
      · exact ⟨factor0_0, 37, outerEdge29_1⟩
    · cases t
      · exact ⟨factor0_0, 38, outerEdge30_0⟩
      · exact ⟨factor0_0, 39, outerEdge30_1⟩
    · cases t
      · exact ⟨factor0_0, 23, outerEdge31_0⟩
      · exact ⟨factor0_0, 40, outerEdge31_1⟩
    · cases t
      · exact ⟨factor0_0, 24, outerEdge32_0⟩
      · exact ⟨factor0_0, 41, outerEdge32_1⟩
    · cases t
      · exact ⟨factor0_0, 26, outerEdge33_0⟩
      · exact ⟨factor7_29, 33, outerEdge33_1⟩
    · cases t
      · exact ⟨factor0_0, 27, outerEdge34_0⟩
      · exact ⟨factor5_46, 32, outerEdge34_1⟩
    · cases t
      · exact ⟨factor0_0, 42, outerEdge35_0⟩
      · exact ⟨factor0_0, 19, outerEdge35_1⟩
    · cases t
      · exact ⟨factor0_0, 43, outerEdge36_0⟩
      · exact ⟨factor0_0, 20, outerEdge36_1⟩
    · cases t
      · exact ⟨factor0_0, 44, outerEdge37_0⟩
      · exact ⟨factor0_0, 38, outerEdge37_1⟩
    · cases t
      · exact ⟨factor0_0, 30, outerEdge38_0⟩
      · exact ⟨factor0_0, 29, outerEdge38_1⟩
    · cases t
      · exact ⟨factor0_0, 45, outerEdge39_0⟩
      · exact ⟨factor0_0, 22, outerEdge39_1⟩
    · cases t
      · exact ⟨factor0_0, 46, outerEdge40_0⟩
      · exact ⟨factor0_0, 47, outerEdge40_1⟩
    · cases t
      · exact ⟨factor0_0, 48, outerEdge41_0⟩
      · exact ⟨factor3_42, 34, outerEdge41_1⟩
    · cases t
      · exact ⟨factor0_0, 35, outerEdge42_0⟩
      · exact ⟨factor0_0, 49, outerEdge42_1⟩
    · cases t
      · exact ⟨factor0_0, 36, outerEdge43_0⟩
      · exact ⟨factor5_43, 42, outerEdge43_1⟩
    · cases t
      · exact ⟨factor0_0, 37, outerEdge44_0⟩
      · exact ⟨factor0_0, 50, outerEdge44_1⟩
    · cases t
      · exact ⟨factor0_0, 39, outerEdge45_0⟩
      · exact ⟨factor0_0, 51, outerEdge45_1⟩
    · cases t
      · exact ⟨factor0_0, 40, outerEdge46_0⟩
      · exact ⟨factor0_0, 52, outerEdge46_1⟩
    · cases t
      · exact ⟨factor2_46, 47, outerEdge47_0⟩
      · exact ⟨factor0_0, 31, outerEdge47_1⟩
    · cases t
      · exact ⟨factor0_0, 41, outerEdge48_0⟩
      · exact ⟨factor2_46, 46, outerEdge48_1⟩
    · cases t
      · exact ⟨factor0_0, 53, outerEdge49_0⟩
      · exact ⟨factor5_43, 43, outerEdge49_1⟩
    · cases t
      · exact ⟨factor0_0, 54, outerEdge50_0⟩
      · exact ⟨factor0_0, 55, outerEdge50_1⟩
    · cases t
      · exact ⟨factor0_0, 56, outerEdge51_0⟩
      · exact ⟨factor0_0, 57, outerEdge51_1⟩
    · cases t
      · exact ⟨factor0_0, 58, outerEdge52_0⟩
      · exact ⟨factor2_46, 48, outerEdge52_1⟩
    · cases t
      · exact ⟨factor0_0, 49, outerEdge53_0⟩
      · exact ⟨factor0_0, 59, outerEdge53_1⟩
    · cases t
      · exact ⟨factor0_0, 50, outerEdge54_0⟩
      · exact ⟨factor0_0, 60, outerEdge54_1⟩
    · cases t
      · exact ⟨factor0_0, 61, outerEdge55_0⟩
      · exact ⟨factor0_0, 44, outerEdge55_1⟩
    · cases t
      · exact ⟨factor0_0, 51, outerEdge56_0⟩
      · exact ⟨factor0_0, 62, outerEdge56_1⟩
    · cases t
      · exact ⟨factor0_0, 63, outerEdge57_0⟩
      · exact ⟨factor0_0, 45, outerEdge57_1⟩
    · cases t
      · exact ⟨factor0_0, 52, outerEdge58_0⟩
      · exact ⟨factor0_0, 64, outerEdge58_1⟩
    · cases t
      · exact ⟨factor0_0, 65, outerEdge59_0⟩
      · exact ⟨factor0_0, 66, outerEdge59_1⟩
    · cases t
      · exact ⟨factor5_43, 66, outerEdge60_0⟩
      · exact ⟨factor0_0, 67, outerEdge60_1⟩
    · cases t
      · exact ⟨factor0_0, 55, outerEdge61_0⟩
      · exact ⟨factor0_0, 68, outerEdge61_1⟩
    · cases t
      · exact ⟨factor0_0, 69, outerEdge62_0⟩
      · exact ⟨factor0_0, 70, outerEdge62_1⟩
    · cases t
      · exact ⟨factor0_0, 57, outerEdge63_0⟩
      · exact ⟨factor0_0, 71, outerEdge63_1⟩
    · cases t
      · exact ⟨factor0_0, 72, outerEdge64_0⟩
      · exact ⟨factor0_0, 73, outerEdge64_1⟩
    · cases t
      · exact ⟨factor0_0, 59, outerEdge65_0⟩
      · exact ⟨factor0_0, 74, outerEdge65_1⟩
    · cases t
      · exact ⟨factor5_43, 60, outerEdge66_0⟩
      · exact ⟨factor0_0, 53, outerEdge66_1⟩
    · cases t
      · exact ⟨factor0_0, 75, outerEdge67_0⟩
      · exact ⟨factor0_0, 54, outerEdge67_1⟩
    · cases t
      · exact ⟨factor0_0, 76, outerEdge68_0⟩
      · exact ⟨factor0_0, 77, outerEdge68_1⟩
    · cases t
      · exact ⟨factor0_0, 62, outerEdge69_0⟩
      · exact ⟨factor0_0, 78, outerEdge69_1⟩
    · cases t
      · exact ⟨factor0_0, 79, outerEdge70_0⟩
      · exact ⟨factor0_0, 56, outerEdge70_1⟩
    · cases t
      · exact ⟨factor0_0, 80, outerEdge71_0⟩
      · exact ⟨factor0_0, 72, outerEdge71_1⟩
    · cases t
      · exact ⟨factor0_0, 64, outerEdge72_0⟩
      · exact ⟨factor0_0, 63, outerEdge72_1⟩
    · cases t
      · exact ⟨factor8_0, 74, outerEdge73_0⟩
      · exact ⟨factor0_0, 58, outerEdge73_1⟩
    · cases t
      · exact ⟨factor3_0, 73, outerEdge74_0⟩
      · exact ⟨factor0_0, 81, outerEdge74_1⟩
    · cases t
      · exact ⟨factor0_0, 67, outerEdge75_0⟩
      · exact ⟨factor0_0, 82, outerEdge75_1⟩
    · cases t
      · exact ⟨factor0_0, 68, outerEdge76_0⟩
      · exact ⟨factor0_0, 83, outerEdge76_1⟩
    · cases t
      · exact ⟨factor0_0, 78, outerEdge77_0⟩
      · exact ⟨factor0_0, 61, outerEdge77_1⟩
    · cases t
      · exact ⟨factor0_0, 77, outerEdge78_0⟩
      · exact ⟨factor0_0, 84, outerEdge78_1⟩
    · cases t
      · exact ⟨factor0_0, 70, outerEdge79_0⟩
      · exact ⟨factor0_0, 85, outerEdge79_1⟩
    · cases t
      · exact ⟨factor0_0, 71, outerEdge80_0⟩
      · exact ⟨factor0_0, 86, outerEdge80_1⟩
    · cases t
      · exact ⟨factor0_0, 87, outerEdge81_0⟩
      · exact ⟨factor0_0, 65, outerEdge81_1⟩
    · cases t
      · exact ⟨factor0_0, 88, outerEdge82_0⟩
      · exact ⟨factor0_0, 89, outerEdge82_1⟩
    · cases t
      · exact ⟨factor0_0, 90, outerEdge83_0⟩
      · exact ⟨factor0_0, 91, outerEdge83_1⟩
    · cases t
      · exact ⟨factor0_0, 92, outerEdge84_0⟩
      · exact ⟨factor0_0, 69, outerEdge84_1⟩
    · cases t
      · exact ⟨factor0_0, 93, outerEdge85_0⟩
      · exact ⟨factor0_0, 94, outerEdge85_1⟩
    · cases t
      · exact ⟨factor0_0, 95, outerEdge86_0⟩
      · exact ⟨factor0_0, 96, outerEdge86_1⟩
    · cases t
      · exact ⟨factor0_0, 81, outerEdge87_0⟩
      · exact ⟨factor0_0, 97, outerEdge87_1⟩
    · cases t
      · exact ⟨factor0_0, 82, outerEdge88_0⟩
      · exact ⟨factor0_0, 98, outerEdge88_1⟩
    · cases t
      · exact ⟨factor0_0, 99, outerEdge89_0⟩
      · exact ⟨factor0_0, 75, outerEdge89_1⟩
    · cases t
      · exact ⟨factor0_0, 83, outerEdge90_0⟩
      · exact ⟨factor0_0, 100, outerEdge90_1⟩
    · cases t
      · exact ⟨factor0_0, 101, outerEdge91_0⟩
      · exact ⟨factor0_0, 76, outerEdge91_1⟩
    · cases t
      · exact ⟨factor0_0, 84, outerEdge92_0⟩
      · exact ⟨factor0_0, 102, outerEdge92_1⟩
    · cases t
      · exact ⟨factor0_0, 85, outerEdge93_0⟩
      · exact ⟨factor0_0, 103, outerEdge93_1⟩
    · cases t
      · exact ⟨factor0_0, 104, outerEdge94_0⟩
      · exact ⟨factor0_0, 79, outerEdge94_1⟩
    · cases t
      · exact ⟨factor0_0, 86, outerEdge95_0⟩
      · exact ⟨factor0_0, 105, outerEdge95_1⟩
    · cases t
      · exact ⟨factor0_0, 106, outerEdge96_0⟩
      · exact ⟨factor0_0, 80, outerEdge96_1⟩
    · cases t
      · exact ⟨factor0_0, 107, outerEdge97_0⟩
      · exact ⟨factor0_0, 108, outerEdge97_1⟩
    · cases t
      · exact ⟨factor0_0, 109, outerEdge98_0⟩
      · exact ⟨factor0_0, 110, outerEdge98_1⟩
    · cases t
      · exact ⟨factor0_0, 89, outerEdge99_0⟩
      · exact ⟨factor0_0, 111, outerEdge99_1⟩
    · cases t
      · exact ⟨factor0_0, 112, outerEdge100_0⟩
      · exact ⟨factor0_0, 113, outerEdge100_1⟩
    · cases t
      · exact ⟨factor0_0, 91, outerEdge101_0⟩
      · exact ⟨factor0_0, 114, outerEdge101_1⟩
    · cases t
      · exact ⟨factor0_0, 115, outerEdge102_0⟩
      · exact ⟨factor0_0, 116, outerEdge102_1⟩
    · cases t
      · exact ⟨factor0_0, 117, outerEdge103_0⟩
      · exact ⟨factor0_0, 118, outerEdge103_1⟩
    · cases t
      · exact ⟨factor0_0, 94, outerEdge104_0⟩
      · exact ⟨factor0_0, 119, outerEdge104_1⟩
    · cases t
      · exact ⟨factor0_0, 120, outerEdge105_0⟩
      · exact ⟨factor0_0, 121, outerEdge105_1⟩
    · cases t
      · exact ⟨factor0_0, 96, outerEdge106_0⟩
      · exact ⟨factor0_0, 122, outerEdge106_1⟩
    · cases t
      · exact ⟨factor0_0, 97, outerEdge107_0⟩
      · exact ⟨factor0_0, 123, outerEdge107_1⟩
    · cases t
      · exact ⟨factor0_0, 124, outerEdge108_0⟩
      · exact ⟨factor0_0, 87, outerEdge108_1⟩
    · cases t
      · exact ⟨factor0_0, 98, outerEdge109_0⟩
      · exact ⟨factor5_43, 124, outerEdge109_1⟩
    · cases t
      · exact ⟨factor0_0, 125, outerEdge110_0⟩
      · exact ⟨factor0_0, 88, outerEdge110_1⟩
    · cases t
      · exact ⟨factor0_0, 126, outerEdge111_0⟩
      · exact ⟨factor0_0, 112, outerEdge111_1⟩
    · cases t
      · exact ⟨factor0_0, 100, outerEdge112_0⟩
      · exact ⟨factor0_0, 99, outerEdge112_1⟩
    · cases t
      · exact ⟨factor0_0, 127, outerEdge113_0⟩
      · exact ⟨factor0_0, 90, outerEdge113_1⟩
    · cases t
      · exact ⟨factor4_36, 114, outerEdge114_0⟩
      · exact ⟨factor0_0, 128, outerEdge114_1⟩
    · cases t
      · exact ⟨factor0_0, 102, outerEdge115_0⟩
      · exact ⟨factor0_0, 129, outerEdge115_1⟩
    · cases t
      · exact ⟨factor0_0, 130, outerEdge116_0⟩
      · exact ⟨factor0_0, 92, outerEdge116_1⟩
    · cases t
      · exact ⟨factor0_0, 103, outerEdge117_0⟩
      · exact ⟨factor0_0, 131, outerEdge117_1⟩
    · cases t
      · exact ⟨factor7_19, 118, outerEdge118_0⟩
      · exact ⟨factor0_0, 93, outerEdge118_1⟩
    · cases t
      · exact ⟨factor0_0, 132, outerEdge119_0⟩
      · exact ⟨factor0_0, 120, outerEdge119_1⟩
    · cases t
      · exact ⟨factor0_0, 105, outerEdge120_0⟩
      · exact ⟨factor0_0, 104, outerEdge120_1⟩
    · cases t
      · exact ⟨factor0_0, 133, outerEdge121_0⟩
      · exact ⟨factor0_0, 95, outerEdge121_1⟩
    · cases t
      · exact ⟨factor0_0, 134, outerEdge122_0⟩
      · exact ⟨factor0_0, 135, outerEdge122_1⟩
    · cases t
      · exact ⟨factor3_0, 135, outerEdge123_0⟩
      · exact ⟨factor0_0, 136, outerEdge123_1⟩
    · cases t
      · exact ⟨factor0_0, 108, outerEdge124_0⟩
      · exact ⟨factor0_0, 137, outerEdge124_1⟩
    · cases t
      · exact ⟨factor0_0, 110, outerEdge125_0⟩
      · exact ⟨factor0_0, 138, outerEdge125_1⟩
    · cases t
      · exact ⟨factor0_0, 111, outerEdge126_0⟩
      · exact ⟨factor0_0, 139, outerEdge126_1⟩
    · cases t
      · exact ⟨factor0_0, 113, outerEdge127_0⟩
      · exact ⟨factor0_0, 140, outerEdge127_1⟩
    · cases t
      · exact ⟨factor0_0, 141, outerEdge128_0⟩
      · exact ⟨factor0_0, 101, outerEdge128_1⟩
    · cases t
      · exact ⟨factor0_0, 142, outerEdge129_0⟩
      · exact ⟨factor0_0, 143, outerEdge129_1⟩
    · cases t
      · exact ⟨factor0_0, 116, outerEdge130_0⟩
      · exact ⟨factor0_0, 144, outerEdge130_1⟩
    · cases t
      · exact ⟨factor0_0, 145, outerEdge131_0⟩
      · exact ⟨factor0_0, 146, outerEdge131_1⟩
    · cases t
      · exact ⟨factor0_0, 119, outerEdge132_0⟩
      · exact ⟨factor0_0, 147, outerEdge132_1⟩
    · cases t
      · exact ⟨factor0_0, 121, outerEdge133_0⟩
      · exact ⟨factor0_0, 148, outerEdge133_1⟩
    · cases t
      · exact ⟨factor0_0, 122, outerEdge134_0⟩
      · exact ⟨factor0_0, 149, outerEdge134_1⟩
    · cases t
      · exact ⟨factor8_0, 123, outerEdge135_0⟩
      · exact ⟨factor0_0, 106, outerEdge135_1⟩
    · cases t
      · exact ⟨factor0_0, 150, outerEdge136_0⟩
      · exact ⟨factor0_0, 107, outerEdge136_1⟩
    · cases t
      · exact ⟨factor0_0, 151, outerEdge137_0⟩
      · exact ⟨factor5_43, 109, outerEdge137_1⟩
    · cases t
      · exact ⟨factor0_0, 152, outerEdge138_0⟩
      · exact ⟨factor0_0, 153, outerEdge138_1⟩
    · cases t
      · exact ⟨factor0_0, 154, outerEdge139_0⟩
      · exact ⟨factor0_0, 155, outerEdge139_1⟩
    · cases t
      · exact ⟨factor0_0, 156, outerEdge140_0⟩
      · exact ⟨factor0_0, 157, outerEdge140_1⟩
    · cases t
      · exact ⟨factor0_0, 128, outerEdge141_0⟩
      · exact ⟨factor0_0, 158, outerEdge141_1⟩
    · cases t
      · exact ⟨factor0_0, 129, outerEdge142_0⟩
      · exact ⟨factor0_0, 141, outerEdge142_1⟩
    · cases t
      · exact ⟨factor0_0, 159, outerEdge143_0⟩
      · exact ⟨factor0_0, 115, outerEdge143_1⟩
    · cases t
      · exact ⟨factor0_0, 160, outerEdge144_0⟩
      · exact ⟨factor0_0, 145, outerEdge144_1⟩
    · cases t
      · exact ⟨factor0_0, 131, outerEdge145_0⟩
      · exact ⟨factor0_0, 130, outerEdge145_1⟩
    · cases t
      · exact ⟨factor0_0, 161, outerEdge146_0⟩
      · exact ⟨factor0_0, 117, outerEdge146_1⟩
    · cases t
      · exact ⟨factor0_0, 162, outerEdge147_0⟩
      · exact ⟨factor0_0, 163, outerEdge147_1⟩
    · cases t
      · exact ⟨factor0_0, 164, outerEdge148_0⟩
      · exact ⟨factor0_0, 165, outerEdge148_1⟩
    · cases t
      · exact ⟨factor0_0, 166, outerEdge149_0⟩
      · exact ⟨factor0_0, 167, outerEdge149_1⟩
    · cases t
      · exact ⟨factor0_0, 136, outerEdge150_0⟩
      · exact ⟨factor0_0, 168, outerEdge150_1⟩
    · cases t
      · exact ⟨factor0_0, 137, outerEdge151_0⟩
      · exact ⟨factor0_0, 169, outerEdge151_1⟩
    · cases t
      · exact ⟨factor0_0, 138, outerEdge152_0⟩
      · exact ⟨factor0_0, 170, outerEdge152_1⟩
    · cases t
      · exact ⟨factor0_0, 171, outerEdge153_0⟩
      · exact ⟨factor0_0, 125, outerEdge153_1⟩
    · cases t
      · exact ⟨factor0_0, 139, outerEdge154_0⟩
      · exact ⟨factor0_0, 172, outerEdge154_1⟩
    · cases t
      · exact ⟨factor0_0, 173, outerEdge155_0⟩
      · exact ⟨factor0_0, 126, outerEdge155_1⟩
    · cases t
      · exact ⟨factor0_0, 140, outerEdge156_0⟩
      · exact ⟨factor0_0, 174, outerEdge156_1⟩
    · cases t
      · exact ⟨factor0_0, 175, outerEdge157_0⟩
      · exact ⟨factor0_0, 127, outerEdge157_1⟩
    · cases t
      · exact ⟨factor0_0, 176, outerEdge158_0⟩
      · exact ⟨factor0_0, 142, outerEdge158_1⟩
    · cases t
      · exact ⟨factor0_0, 143, outerEdge159_0⟩
      · exact ⟨factor0_0, 177, outerEdge159_1⟩
    · cases t
      · exact ⟨factor0_0, 144, outerEdge160_0⟩
      · exact ⟨factor0_0, 178, outerEdge160_1⟩
    · cases t
      · exact ⟨factor0_0, 146, outerEdge161_0⟩
      · exact ⟨factor0_0, 179, outerEdge161_1⟩
    · cases t
      · exact ⟨factor0_0, 147, outerEdge162_0⟩
      · exact ⟨factor7_19, 161, outerEdge162_1⟩
    · cases t
      · exact ⟨factor0_0, 180, outerEdge163_0⟩
      · exact ⟨factor0_0, 132, outerEdge163_1⟩
    · cases t
      · exact ⟨factor0_0, 148, outerEdge164_0⟩
      · exact ⟨factor0_0, 181, outerEdge164_1⟩
    · cases t
      · exact ⟨factor0_0, 182, outerEdge165_0⟩
      · exact ⟨factor0_0, 133, outerEdge165_1⟩
    · cases t
      · exact ⟨factor0_0, 149, outerEdge166_0⟩
      · exact ⟨factor0_0, 183, outerEdge166_1⟩
    · cases t
      · exact ⟨factor0_0, 184, outerEdge167_0⟩
      · exact ⟨factor0_0, 134, outerEdge167_1⟩
    · cases t
      · exact ⟨factor0_0, 185, outerEdge168_0⟩
      · exact ⟨factor0_0, 186, outerEdge168_1⟩
    · cases t
      · exact ⟨factor0_0, 187, outerEdge169_0⟩
      · exact ⟨factor0_0, 188, outerEdge169_1⟩
    · cases t
      · exact ⟨factor0_0, 189, outerEdge170_0⟩
      · exact ⟨factor7_11, 184, outerEdge170_1⟩
    · cases t
      · exact ⟨factor0_0, 153, outerEdge171_0⟩
      · exact ⟨factor0_0, 190, outerEdge171_1⟩
    · cases t
      · exact ⟨factor0_0, 191, outerEdge172_0⟩
      · exact ⟨factor0_0, 192, outerEdge172_1⟩
    · cases t
      · exact ⟨factor0_0, 155, outerEdge173_0⟩
      · exact ⟨factor0_0, 193, outerEdge173_1⟩
    · cases t
      · exact ⟨factor0_0, 194, outerEdge174_0⟩
      · exact ⟨factor0_0, 195, outerEdge174_1⟩
    · cases t
      · exact ⟨factor0_0, 157, outerEdge175_0⟩
      · exact ⟨factor0_0, 196, outerEdge175_1⟩
    · cases t
      · exact ⟨factor0_0, 158, outerEdge176_0⟩
      · exact ⟨factor4_36, 175, outerEdge176_1⟩
    · cases t
      · exact ⟨factor0_0, 197, outerEdge177_0⟩
      · exact ⟨factor0_0, 198, outerEdge177_1⟩
    · cases t
      · exact ⟨factor0_0, 199, outerEdge178_0⟩
      · exact ⟨factor0_0, 200, outerEdge178_1⟩
    · cases t
      · exact ⟨factor0_0, 201, outerEdge179_0⟩
      · exact ⟨factor7_19, 162, outerEdge179_1⟩
    · cases t
      · exact ⟨factor0_0, 163, outerEdge180_0⟩
      · exact ⟨factor0_0, 202, outerEdge180_1⟩
    · cases t
      · exact ⟨factor0_0, 203, outerEdge181_0⟩
      · exact ⟨factor0_0, 204, outerEdge181_1⟩
    · cases t
      · exact ⟨factor0_0, 165, outerEdge182_0⟩
      · exact ⟨factor0_0, 205, outerEdge182_1⟩
    · cases t
      · exact ⟨factor0_0, 206, outerEdge183_0⟩
      · exact ⟨factor0_0, 207, outerEdge183_1⟩
    · cases t
      · exact ⟨factor0_0, 167, outerEdge184_0⟩
      · exact ⟨factor1_49, 152, outerEdge184_1⟩
    · cases t
      · exact ⟨factor0_0, 168, outerEdge185_0⟩
      · exact ⟨factor0_0, 208, outerEdge185_1⟩
    · cases t
      · exact ⟨factor0_0, 209, outerEdge186_0⟩
      · exact ⟨factor0_0, 150, outerEdge186_1⟩
    · cases t
      · exact ⟨factor0_0, 169, outerEdge187_0⟩
      · exact ⟨factor0_0, 210, outerEdge187_1⟩
    · cases t
      · exact ⟨factor0_0, 211, outerEdge188_0⟩
      · exact ⟨factor0_0, 151, outerEdge188_1⟩
    · cases t
      · exact ⟨factor0_0, 170, outerEdge189_0⟩
      · exact ⟨factor0_0, 212, outerEdge189_1⟩
    · cases t
      · exact ⟨factor0_0, 213, outerEdge190_0⟩
      · exact ⟨factor0_0, 191, outerEdge190_1⟩
    · cases t
      · exact ⟨factor0_0, 172, outerEdge191_0⟩
      · exact ⟨factor0_0, 171, outerEdge191_1⟩
    · cases t
      · exact ⟨factor0_0, 214, outerEdge192_0⟩
      · exact ⟨factor0_0, 154, outerEdge192_1⟩
    · cases t
      · exact ⟨factor7_55, 193, outerEdge193_0⟩
      · exact ⟨factor0_0, 215, outerEdge193_1⟩
    · cases t
      · exact ⟨factor0_0, 174, outerEdge194_0⟩
      · exact ⟨factor0_0, 216, outerEdge194_1⟩
    · cases t
      · exact ⟨factor0_0, 217, outerEdge195_0⟩
      · exact ⟨factor0_0, 156, outerEdge195_1⟩
    · cases t
      · exact ⟨factor0_0, 218, outerEdge196_0⟩
      · exact ⟨factor4_36, 176, outerEdge196_1⟩
    · cases t
      · exact ⟨factor0_0, 177, outerEdge197_0⟩
      · exact ⟨factor0_0, 219, outerEdge197_1⟩
    · cases t
      · exact ⟨factor0_0, 220, outerEdge198_0⟩
      · exact ⟨factor0_0, 159, outerEdge198_1⟩
    · cases t
      · exact ⟨factor0_0, 178, outerEdge199_0⟩
      · exact ⟨factor0_0, 221, outerEdge199_1⟩
    · cases t
      · exact ⟨factor0_0, 222, outerEdge200_0⟩
      · exact ⟨factor0_0, 160, outerEdge200_1⟩
    · cases t
      · exact ⟨factor0_0, 179, outerEdge201_0⟩
      · exact ⟨factor0_0, 223, outerEdge201_1⟩
    · cases t
      · exact ⟨factor0_0, 224, outerEdge202_0⟩
      · exact ⟨factor0_0, 225, outerEdge202_1⟩
    · cases t
      · exact ⟨factor0_0, 181, outerEdge203_0⟩
      · exact ⟨factor0_0, 226, outerEdge203_1⟩
    · cases t
      · exact ⟨factor9_17, 204, outerEdge204_0⟩
      · exact ⟨factor0_0, 164, outerEdge204_1⟩
    · cases t
      · exact ⟨factor0_0, 227, outerEdge205_0⟩
      · exact ⟨factor0_0, 206, outerEdge205_1⟩
    · cases t
      · exact ⟨factor0_0, 183, outerEdge206_0⟩
      · exact ⟨factor0_0, 182, outerEdge206_1⟩
    · cases t
      · exact ⟨factor0_0, 228, outerEdge207_0⟩
      · exact ⟨factor0_0, 166, outerEdge207_1⟩
    · cases t
      · exact ⟨factor0_0, 229, outerEdge208_0⟩
      · exact ⟨factor0_0, 230, outerEdge208_1⟩
    · cases t
      · exact ⟨factor0_0, 186, outerEdge209_0⟩
      · exact ⟨factor0_0, 231, outerEdge209_1⟩
    · cases t
      · exact ⟨factor0_0, 232, outerEdge210_0⟩
      · exact ⟨factor0_0, 233, outerEdge210_1⟩
    · cases t
      · exact ⟨factor0_0, 188, outerEdge211_0⟩
      · exact ⟨factor0_0, 234, outerEdge211_1⟩
    · cases t
      · exact ⟨factor0_0, 235, outerEdge212_0⟩
      · exact ⟨factor5_28, 229, outerEdge212_1⟩
    · cases t
      · exact ⟨factor0_0, 190, outerEdge213_0⟩
      · exact ⟨factor0_0, 236, outerEdge213_1⟩
    · cases t
      · exact ⟨factor0_0, 192, outerEdge214_0⟩
      · exact ⟨factor0_0, 237, outerEdge214_1⟩
    · cases t
      · exact ⟨factor0_0, 216, outerEdge215_0⟩
      · exact ⟨factor0_0, 173, outerEdge215_1⟩
    · cases t
      · exact ⟨factor0_0, 215, outerEdge216_0⟩
      · exact ⟨factor0_0, 238, outerEdge216_1⟩
    · cases t
      · exact ⟨factor0_0, 195, outerEdge217_0⟩
      · exact ⟨factor9_35, 217, outerEdge217_1⟩
    · cases t
      · exact ⟨factor0_0, 196, outerEdge218_0⟩
      · exact ⟨factor0_0, 239, outerEdge218_1⟩
    · cases t
      · exact ⟨factor5_52, 237, outerEdge219_0⟩
      · exact ⟨factor0_0, 240, outerEdge219_1⟩
    · cases t
      · exact ⟨factor0_0, 198, outerEdge220_0⟩
      · exact ⟨factor10_51, 213, outerEdge220_1⟩
    · cases t
      · exact ⟨factor10_51, 236, outerEdge221_0⟩
      · exact ⟨factor1_14, 228, outerEdge221_1⟩
    · cases t
      · exact ⟨factor0_0, 200, outerEdge222_0⟩
      · exact ⟨factor0_0, 241, outerEdge222_1⟩
    · cases t
      · exact ⟨factor0_0, 242, outerEdge223_0⟩
      · exact ⟨factor0_0, 243, outerEdge223_1⟩
    · cases t
      · exact ⟨factor0_0, 202, outerEdge224_0⟩
      · exact ⟨factor0_6, 224, outerEdge224_1⟩
    · cases t
      · exact ⟨factor0_0, 226, outerEdge225_0⟩
      · exact ⟨factor0_0, 180, outerEdge225_1⟩
    · cases t
      · exact ⟨factor0_0, 225, outerEdge226_0⟩
      · exact ⟨factor0_0, 244, outerEdge226_1⟩
    · cases t
      · exact ⟨factor0_0, 205, outerEdge227_0⟩
      · exact ⟨factor6_11, 242, outerEdge227_1⟩
    · cases t
      · exact ⟨factor0_0, 207, outerEdge228_0⟩
      · exact ⟨factor9_6, 199, outerEdge228_1⟩
    · cases t
      · exact ⟨factor0_0, 208, outerEdge229_0⟩
      · exact ⟨factor4_49, 189, outerEdge229_1⟩
    · cases t
      · exact ⟨factor0_0, 245, outerEdge230_0⟩
      · exact ⟨factor0_0, 185, outerEdge230_1⟩
    · cases t
      · exact ⟨factor0_0, 246, outerEdge231_0⟩
      · exact ⟨factor0_0, 232, outerEdge231_1⟩
    · cases t
      · exact ⟨factor0_0, 210, outerEdge232_0⟩
      · exact ⟨factor0_0, 209, outerEdge232_1⟩
    · cases t
      · exact ⟨factor0_0, 247, outerEdge233_0⟩
      · exact ⟨factor0_0, 187, outerEdge233_1⟩
    · cases t
      · exact ⟨factor0_0, 248, outerEdge234_0⟩
      · exact ⟨factor5_43, 235, outerEdge234_1⟩
    · cases t
      · exact ⟨factor0_0, 212, outerEdge235_0⟩
      · exact ⟨factor5_43, 211, outerEdge235_1⟩
    · cases t
      · exact ⟨factor9_36, 221, outerEdge236_0⟩
      · exact ⟨factor9_36, 220, outerEdge236_1⟩
    · cases t
      · exact ⟨factor8_40, 219, outerEdge237_0⟩
      · exact ⟨factor0_0, 249, outerEdge237_1⟩
    · cases t
      · exact ⟨factor9_35, 239, outerEdge238_0⟩
      · exact ⟨factor0_0, 194, outerEdge238_1⟩
    · cases t
      · exact ⟨factor7_56, 238, outerEdge239_0⟩
      · exact ⟨factor0_0, 250, outerEdge239_1⟩
    · cases t
      · exact ⟨factor9_49, 240, outerEdge240_0⟩
      · exact ⟨factor0_0, 197, outerEdge240_1⟩
    · cases t
      · exact ⟨factor4_51, 241, outerEdge241_0⟩
      · exact ⟨factor0_0, 251, outerEdge241_1⟩
    · cases t
      · exact ⟨factor0_0, 223, outerEdge242_0⟩
      · exact ⟨factor0_0, 252, outerEdge242_1⟩
    · cases t
      · exact ⟨factor7_41, 244, outerEdge243_0⟩
      · exact ⟨factor0_0, 201, outerEdge243_1⟩
    · cases t
      · exact ⟨factor2_38, 243, outerEdge244_0⟩
      · exact ⟨factor0_0, 203, outerEdge244_1⟩
    · cases t
      · exact ⟨factor0_0, 230, outerEdge245_0⟩
      · exact ⟨factor0_0, 253, outerEdge245_1⟩
    · cases t
      · exact ⟨factor0_0, 231, outerEdge246_0⟩
      · exact ⟨factor0_0, 254, outerEdge246_1⟩
    · cases t
      · exact ⟨factor0_0, 233, outerEdge247_0⟩
      · exact ⟨factor0_0, 255, outerEdge247_1⟩
    · cases t
      · exact ⟨factor0_0, 234, outerEdge248_0⟩
      · exact ⟨factor0_0, 256, outerEdge248_1⟩
    · cases t
      · exact ⟨factor0_23, 250, outerEdge249_0⟩
      · exact ⟨factor0_0, 214, outerEdge249_1⟩
    · cases t
      · exact ⟨factor9_14, 249, outerEdge250_0⟩
      · exact ⟨factor0_0, 218, outerEdge250_1⟩
    · cases t
      · exact ⟨factor0_0, 252, outerEdge251_0⟩
      · exact ⟨factor0_0, 222, outerEdge251_1⟩
    · cases t
      · exact ⟨factor0_0, 251, outerEdge252_0⟩
      · exact ⟨factor7_47, 227, outerEdge252_1⟩
    · cases t
      · exact ⟨factor0_0, 257, outerEdge253_0⟩
      · exact ⟨factor0_0, 258, outerEdge253_1⟩
    · cases t
      · exact ⟨factor0_0, 259, outerEdge254_0⟩
      · exact ⟨factor0_0, 260, outerEdge254_1⟩
    · cases t
      · exact ⟨factor2_15, 256, outerEdge255_0⟩
      · exact ⟨factor0_0, 261, outerEdge255_1⟩
    · cases t
      · exact ⟨factor0_58, 255, outerEdge256_0⟩
      · exact ⟨factor0_0, 262, outerEdge256_1⟩
    · cases t
      · exact ⟨factor0_0, 253, outerEdge257_0⟩
      · exact ⟨factor0_0, 263, outerEdge257_1⟩
    · cases t
      · exact ⟨factor10_23, 260, outerEdge258_0⟩
      · exact ⟨factor0_0, 245, outerEdge258_1⟩
    · cases t
      · exact ⟨factor0_0, 254, outerEdge259_0⟩
      · exact ⟨factor10_23, 259, outerEdge259_1⟩
    · cases t
      · exact ⟨factor10_34, 258, outerEdge260_0⟩
      · exact ⟨factor0_0, 246, outerEdge260_1⟩
    · cases t
      · exact ⟨factor0_0, 264, outerEdge261_0⟩
      · exact ⟨factor0_0, 247, outerEdge261_1⟩
    · cases t
      · exact ⟨factor0_0, 265, outerEdge262_0⟩
      · exact ⟨factor0_0, 248, outerEdge262_1⟩
    · cases t
      · exact ⟨factor6_31, 263, outerEdge263_0⟩
      · exact ⟨factor4_22, 265, outerEdge263_1⟩
    · cases t
      · exact ⟨factor0_0, 261, outerEdge264_0⟩
      · exact ⟨factor2_15, 264, outerEdge264_1⟩
    · cases t
      · exact ⟨factor0_0, 262, outerEdge265_0⟩
      · exact ⟨factor6_48, 257, outerEdge265_1⟩)

public theorem card_H_le : Nat.card H ≤ 660 := by
  have h := (innerCover.finite_card_le inner_generates).2
  simpa only [Nat.card_zpowers, orderOf_hz, Nat.card_fin] using h

public theorem card_model_le : Nat.card Model ≤ 175560 := by
  have h := (outerCover.finite_card_le outer_generates).2
  simp only [Nat.card_fin] at h
  exact h.trans (Nat.mul_le_mul_right 266 card_H_le)

end Janko1.OrderCertificate
