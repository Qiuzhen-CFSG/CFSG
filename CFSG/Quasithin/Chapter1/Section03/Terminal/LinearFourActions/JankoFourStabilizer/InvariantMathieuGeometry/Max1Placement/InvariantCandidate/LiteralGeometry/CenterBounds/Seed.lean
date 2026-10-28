module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.CenterBounds.Pair
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.FixedSpaces.Native
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness.Octad
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness.Octad
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.FixedSpaces.Native
import all Theory.Mathieu.M24.LocalGeometry.LinearFourCore

/-!
# The two center bounds on the seed octad

The 28 octad duads lie in the center of the residual two-core by the
published seed-witness argument. The regular translation action on the
sixteen complementary points expresses their 120 duads as commutators
with kernel vectors. They therefore also lie in the residual two-core.
The 148 distinct vectors exclude central elements outside the kernel under
the individual fixed-space bound. Fixing all octad duads forces pointwise
fixation of the octad, so the centralizer maps into its two-core.

The small finite certificates use the actual native translation permutations.
The internal imports reuse the residual commutator lemmas and evaluate these
permutations without changing any shared definition or public boundary.

Source: Aschbacher–Smith A.3.12(17), pp.47–48, and the local configuration
in 1.3.9, p.514; GLS3 Tables 5.3e and 5.3i. The duad membership argument
extends `AmbientGeometry.LiteralCentralizer.SeedWitness.Octad`.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.OctadCenter
open AmbientGeometry.SeedDuads LiteralBinary
attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

private theorem seed_values : LinearFourCore.seedOctad.val = {0, 1, 2, 3, 4, 5, 11, 17} := by
  ext i
  rw [LinearFourCore.mem_seedOctad]
  simp_rw [m23PointEmbedding_apply]
  revert i
  decide +kernel

private theorem third_point (i j : Fin 24) :
    ∃ k ∈ LinearFourCore.seedOctad.val, k ≠ i ∧ k ≠ j := by
  rw [seed_values]
  revert i j
  decide +kernel

/-- Every duad within the octad lies in the center of the residual two-core. -/
theorem seed_duad_mem_center (i j : LinearFourCore.seedOctad.val) :
    duad i.val j.val ∈ coreCenter (literalOctadResidual LinearFourCore.seedOctad) := by
  obtain ⟨k, hk, hki, hkj⟩ := third_point i.val j.val
  have hik : i ≠ (⟨k, hk⟩ : LinearFourCore.seedOctad.val) := by
    intro h; exact hki (congrArg Subtype.val h).symm
  have hjk : j ≠ (⟨k, hk⟩ : LinearFourCore.seedOctad.val) := by
    intro h; exact hkj (congrArg Subtype.val h).symm
  exact ⟨core_intersection_le _ ⟨duad_mem_core _ _,
    duad_mem_seed_residual i j ⟨k, hk⟩ hik hjk⟩, duad_centralizes_seed_core i j⟩

private theorem complement_transitive (i j : Fin 24)
    (hi : i ∉ LinearFourCore.seedOctad.val) (hj : j ∉ LinearFourCore.seedOctad.val) :
    ∃ n : Fin 16, nativePerm n i = j := by
  rw [seed_values] at hi hj
  have hc : ∀ i j : Fin 24, i ∉ ({0, 1, 2, 3, 4, 5, 11, 17} : Finset (Fin 24)) →
      j ∉ ({0, 1, 2, 3, 4, 5, 11, 17} : Finset (Fin 24)) →
      ∃ n : Fin 16, nativePerm n i = j := by
    decide +kernel
  exact hc i j hi hj

private theorem complement_duad_mem (i j : Fin 24)
    (hi : i ∉ LinearFourCore.seedOctad.val) (hj : j ∉ LinearFourCore.seedOctad.val) :
    duad i j ∈ (literalOctadResidual LinearFourCore.seedOctad).pCoreIn 2 := by
  obtain ⟨n, hn⟩ := complement_transitive i j hi hj
  obtain ⟨x, hx⟩ := literalMathieuMap_surjective (nativeTranslation n)
  have hxp : x ∈ literalOctadPreimage LinearFourCore.seedOctad := by
    change literalMathieuMap x ∈ octadStabilizer LinearFourCore.seedOctad
    rw [hx]
    exact pCoreIn_le _ _ (nativeTranslation_mem n)
  have hxi : literalMathieuMap x • i = j := by
    simpa only [hx, Subgroup.smul_def, Equiv.Perm.smul_def, nativeTranslation_coe] using hn
  have hx0 : literalMathieuMap x • (0 : Fin 24) = 0 := by
    rw [hx]
    change (nativeTranslation n : Equiv.Perm (Fin 24)) 0 = 0
    rw [nativeTranslation_coe]
    rfl
  have he : ⁅x, duad i 0⁆ = duad j i := by
    change x * duad i 0 * x⁻¹ * (duad i 0)⁻¹ = _
    rw [conjugate_duad, hxi, hx0, duad_inv, duad_mul]
  have hm := commutator_mem_residual LinearFourCore.seedOctad x (duad i 0)
    hxp (core_le_preimage _ (duad_mem_core _ _))
  rw [he, duad_symm j i] at hm
  exact core_intersection_le _ ⟨duad_mem_core _ _, hm⟩

private abbrev SamePartPairs := {p : Fin 24 × Fin 24 // p.1 < p.2 ∧
  (p.1 ∈ LinearFourCore.seedOctad.val ↔ p.2 ∈ LinearFourCore.seedOctad.val)}

private theorem samePartPairs_card : Nat.card SamePartPairs = 148 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {p : Fin 24 × Fin 24 // p.1 < p.2 ∧
    (p.1 ∈ LinearFourCore.seedOctad.val ↔ p.2 ∈ LinearFourCore.seedOctad.val)} = 148
  rw [seed_values]
  decide +kernel

private theorem samePart_duad_mem (p : SamePartPairs) :
    duad p.val.1 p.val.2 ∈ (literalOctadResidual LinearFourCore.seedOctad).pCoreIn 2 := by
  by_cases hi : p.val.1 ∈ LinearFourCore.seedOctad.val
  · exact (seed_duad_mem_center ⟨_, hi⟩ ⟨_, p.property.2.mp hi⟩).1
  · exact complement_duad_mem _ _ hi (fun h => hi (p.property.2.mpr h))

/-- The residual two-core contains 148 distinct kernel duads. Hence a central
nonkernel element would violate the individual fixed-space bound. -/
theorem seed_center_le_core (hfixed : LiteralOctadElementFixedBound) :
    coreCenter (literalOctadResidual LinearFourCore.seedOctad) ≤
      pCore 2 certifiedMathieuSubgroup := by
  intro z hz
  by_contra hnz
  have hzq : z ∈ literalOctadTwoPreimage LinearFourCore.seedOctad := by
    change literalMathieuMap z ∈ (octadStabilizer LinearFourCore.seedOctad).pCoreIn 2
    rw [← literalOctadResidual_coreImage]
    exact mem_map_of_mem literalMathieuMap hz.1
  have hc := hfixed LinearFourCore.seedOctad z hzq hnz
  let f : SamePartPairs → (centralizer ({z} : Set certifiedMathieuSubgroup)).subgroupOf
      (pCore 2 certifiedMathieuSubgroup) := fun p =>
    ⟨⟨duad p.val.1 p.val.2, duad_mem_core _ _⟩, by
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact (hz.2 _ (samePart_duad_mem p)).symm⟩
  have hf : Function.Injective f := by
    intro a b h
    have hd : duad a.val.1 a.val.2 = duad b.val.1 b.val.2 :=
      congrArg (fun t => t.val.val) h
    rcases duad_endpoints a.property.1.ne hd with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have ha := a.property.1
      have hb := b.property.1
      rw [h.1, h.2] at ha
      exact False.elim (lt_asymm ha hb)
  have hl := Nat.card_le_card_of_injective f hf
  rw [samePartPairs_card] at hl
  omega

/-- Fixing every central octad duad fixes the octad pointwise, and so places
the quotient image in its intrinsic two-core. -/
theorem seed_centralizer_le_preimage :
    centralizer (coreCenter (literalOctadResidual LinearFourCore.seedOctad) :
      Set certifiedMathieuSubgroup) ≤ literalOctadTwoPreimage LinearFourCore.seedOctad := by
  intro x hx
  have hduad (i j : LinearFourCore.seedOctad.val) :
      duad i.val j.val = duad (literalMathieuMap x • i.val) (literalMathieuMap x • j.val) := by
    rw [← conjugate_duad, ← hx _ (seed_duad_mem_center i j), mul_assoc, mul_inv_cancel, mul_one]
  have hchoice (i j : LinearFourCore.seedOctad.val) (hij : i ≠ j) :
      literalMathieuMap x • i.val = i.val ∨ literalMathieuMap x • i.val = j.val := by
    have hn : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases duad_endpoints hn (hduad i j) with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.2.symm
  let a : LinearFourCore.seedOctad.val := ⟨0, by rw [seed_values]; decide⟩
  let b : LinearFourCore.seedOctad.val := ⟨1, by rw [seed_values]; decide⟩
  let c : LinearFourCore.seedOctad.val := ⟨2, by rw [seed_values]; decide⟩
  have hfixa : literalMathieuMap x • a.val = a.val := by
    rcases hchoice a b (by decide) with h | h
    · exact h
    · rcases hchoice a c (by decide) with h' | h'
      · exact h'
      · exact False.elim ((by decide : b.val ≠ c.val) (h.symm.trans h'))
  have hfix (i : Fin 24) (hi : i ∈ LinearFourCore.seedOctad.val) :
      literalMathieuMap x • i = i := by
    by_cases hai : a.val = i
    · simpa only [hai] using hfixa
    · rcases duad_endpoints hai (hduad a ⟨i, hi⟩) with h | h
      · exact h.2.symm
      · exact False.elim (hai (hfixa.symm.trans h.2.symm))
  have hxp : literalMathieuMap x ∈ octadStabilizer LinearFourCore.seedOctad := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    rw [hfix i hi]
    exact hi
  have hk : (⟨literalMathieuMap x, hxp⟩ : octadStabilizer LinearFourCore.seedOctad) ∈
      (LinearFourCore.action LinearFourCore.seedOctad).ker :=
    (LinearFourCore.mem_action_ker _ _).mpr hfix
  change literalMathieuMap x ∈ (octadStabilizer LinearFourCore.seedOctad).pCoreIn 2
  rw [pCoreIn, seed_core_eq_kernel]
  exact mem_map_of_mem _ hk

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.OctadCenter
