module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.LocalKernel
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
import all Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.Comparison

/-!
# Equivariance of the marked 276 star pairs

This proof extension exposes the pair compatibility already established in
`Image.Comparison`, using `import all` only for that private proof. The actual
kernel seed is the pair {0,1}. Its stabilizer is therefore a genuine preimage
under the certified Mathieu quotient; no order-based recognition is involved.

Source: ATLAS J4G1-max1W1 and the checked star labels of `Image.StarData`;
Aschbacher--Smith 16.1.5(9), printed p.1172.
-/

public section
namespace Janko4.Cardinality.QuotientCount.Image

/-- The certified star comparison intertwines every evaluated pair label. -/
theorem actionImageEquivStarGroup_pair
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (a : ActionImage hA hB) (i j : Fin 24) :
    a.val (Simplicity.Max1Fusion.KernelOrbits.maskValue hA hB (pairLabel i j)) =
      Simplicity.Max1Fusion.KernelOrbits.maskValue hA hB
        (pairLabel ((actionImageEquivStarGroup hA hB a).val i)
          ((actionImageEquivStarGroup hA hB a).val j)) := by
  obtain ⟨p, hp⟩ : a.val ∈ (firstProjection hA hB).range := by
    rw [firstProjection_range]
    exact a.property
  have ha : a = ⟨firstProjection hA hB p,
      by rw [← firstProjection_range]; exact ⟨p, rfl⟩⟩ := Subtype.ext hp.symm
  subst a
  rw [actionImageEquivStarGroup_paired]
  exact paired_compatible hA hB p.val p.property i j

end Janko4.Cardinality.QuotientCount.Image

namespace Janko4.InvolutionCentralizers.Second
open Subgroup Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
open scoped Pointwise

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed localKernel

/-- The star permutation induced by actual conjugation in max1. -/
@[expose] noncomputable def starHom : Local →* StarGroup :=
  (actionImageEquivStarGroup matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (action matrixA_mul_self matrixB_pow_four).rangeRestrict

theorem starHom_surjective : Function.Surjective starHom :=
  (actionImageEquivStarGroup _ _).surjective.comp (action _ _).rangeRestrict_surjective

/-- Conjugation on the actual binary kernel is the certified action on pairs. -/
theorem starHom_pair (g : Local) (i j : Fin 24) :
    action matrixA_mul_self matrixB_pow_four g
      (Simplicity.Max1Fusion.KernelOrbits.maskValue matrixA_mul_self matrixB_pow_four (pairLabel i j)) =
      Simplicity.Max1Fusion.KernelOrbits.maskValue matrixA_mul_self matrixB_pow_four
        (pairLabel ((starHom g).val i) ((starHom g).val j)) :=
  actionImageEquivStarGroup_pair matrixA_mul_self matrixB_pow_four
    ((action matrixA_mul_self matrixB_pow_four).rangeRestrict g) i j

private theorem pairLabel_one_iff (i j : Fin 24) :
    pairLabel i j = 1 ↔ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  revert i j
  decide +kernel

/-- The literal pair labelling the seed, before Mathieu relabelling. -/
@[expose] def starPair : Finset (Fin 24) := {0, 1}

/-- Setwise, rather than pointwise, stabilization of the marked star pair. -/
@[expose] def starPairStabilizer : Subgroup StarGroup := MulAction.stabilizer StarGroup starPair

private theorem starPair_mem_iff (p : StarGroup) :
    p ∈ starPairStabilizer ↔ pairLabel (p.val 0) (p.val 1) = 1 := by
  rw [pairLabel_one_iff]
  constructor
  · intro hp
    have h := MulAction.mem_stabilizer_finset'.mp hp
    have h0 : p.val 0 = 0 ∨ p.val 0 = 1 := by
      have h0 := h (b := 0) (by simp [starPair])
      change p.val 0 ∈ starPair at h0
      simpa only [starPair, Finset.mem_insert, Finset.mem_singleton] using h0
    have h1 : p.val 1 = 0 ∨ p.val 1 = 1 := by
      have h1 := h (b := 1) (by simp [starPair])
      change p.val 1 ∈ starPair at h1
      simpa only [starPair, Finset.mem_insert, Finset.mem_singleton] using h1
    have hne : p.val 0 ≠ p.val 1 := p.val.injective.ne (by decide)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact False.elim (hne (h0.trans h1.symm))
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact False.elim (hne (h0.trans h1.symm))
  · rintro (⟨h0,h1⟩ | ⟨h0,h1⟩) <;>
      apply MulAction.mem_stabilizer_finset'.mpr <;>
      intro i hi <;>
      rcases (show i = 0 ∨ i = 1 by simpa [starPair] using hi) with rfl | rfl <;>
      change p.val _ ∈ starPair <;> simp [starPair, h0, h1]

/-- The actual seed centralizer is exactly the preimage of its pair stabilizer. -/
theorem mem_localCentralizer_iff_star (g : Local) :
    g ∈ localCentralizer ↔ starHom g ∈ starPairStabilizer := by
  rw [starPair_mem_iff]
  have h := congrArg (fun z : localKernel matrixA_mul_self matrixB_pow_four => (z : Local))
    (starHom_pair g 0 1)
  rw [action_apply, show pairLabel 0 1 = 1 from rfl, maskValue_one] at h
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have he : Simplicity.Max1Fusion.KernelOrbits.maskValue matrixA_mul_self matrixB_pow_four
        (pairLabel ((starHom g).val 0) ((starHom g).val 1)) =
        Simplicity.Max1Fusion.KernelOrbits.maskValue matrixA_mul_self matrixB_pow_four 1 := by
      apply Subtype.ext
      rw [maskValue_one, ← h, hg]
      simp [mul_assoc]
    exact maskValue_injective_bounded _ _ (pairLabel_lt _ _) (by decide) he
  · intro he
    rw [he, maskValue_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h

/-- Subgroup form of the marked stabilizer identification. -/
theorem localCentralizer_eq_preimage :
    localCentralizer = starPairStabilizer.comap starHom := by
  ext g
  exact mem_localCentralizer_iff_star g

/-- The quotient map restricted to the literal pair stabilizer. -/
@[expose] noncomputable def toStarPair : localCentralizer →* starPairStabilizer where
  toFun g := ⟨starHom g.val, (mem_localCentralizer_iff_star g.val).mp g.property⟩
  map_one' := Subtype.ext (map_one starHom)
  map_mul' g h := Subtype.ext (map_mul starHom g.val h.val)

theorem toStarPair_surjective : Function.Surjective toStarPair := by
  intro p
  obtain ⟨g, hg⟩ := starHom_surjective p.val
  exact ⟨⟨g, (mem_localCentralizer_iff_star g).mpr (hg ▸ p.property)⟩, Subtype.ext hg⟩

end Janko4.InvolutionCentralizers.Second
