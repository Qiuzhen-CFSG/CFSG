module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2FixedLifting

/-!
# Centralization from the original G₂ natural coordinates

For the literal Weyl marking used in the binary G₂ source assembly, a
subgroup of L centralizes a subgroup of V exactly when its marked derived
action fixes their natural images. The same statement holds for the full
normalizer actor constructed in `NormalizerAction`, with its original
conjugation coordinates retained. Fixed lifting retains the central line.

Source: Aschbacher--Smith B.4.6(7) and the G₂ row of 12.4.2, pp.88,812.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource Atlas.G2.Natural

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V A W : Subgroup G}

/-- Natural fixed-space calculations discharge centralization on the whole
original subgroup, for actors lying in L. No structural or normalizer-control
input is needed for this transport. -/
theorem centralizes_iff_natural_fixed
    (D : ChosenModule T L V)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hAL : A ≤ L) (hWV : W ≤ V) :
    W ≤ centralizer (A : Set G) ↔
      ∀ (a : A) (w : W),
        derivedAction (ZMod 2)
          (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) (inclusion hAL a)))
          (mk (ZMod 2) (e.linearEquiv
            (D.spaceEquiv.symm (inclusion hWV w)).toAdd)) =
        mk (ZMod 2) (e.linearEquiv
          (D.spaceEquiv.symm (inclusion hWV w)).toAdd) := by
  constructor
  · intro hc a w
    apply (g2_weyl_chosen_mem_centralizer_iff_natural_fixed D e
      (inclusion hAL a) (inclusion hWV w)).mp
    exact mem_centralizer_singleton_iff.mpr (hc w.property a a.property).symm
  · intro hf w hw a ha
    have hc := (g2_weyl_chosen_mem_centralizer_iff_natural_fixed D e
      (inclusion hAL ⟨a, ha⟩) (inclusion hWV ⟨w, hw⟩)).mpr (hf ⟨a, ha⟩ ⟨w, hw⟩)
    exact (mem_centralizer_singleton_iff.mp hc).symm

omit [Finite G] in
/-- The marked full normalizer action detects centralization on V from the
natural quotient. This applies to the outer actors as well as to L/O₂(L). -/
theorem normalizer_actor_mem_centralizer_iff_natural_fixed
    (b : V ≃* Multiplicative (TraceZero (ZMod 2)))
    (φ : normalizer (L : Set G) →* Atlas.G2.Model (ZMod 2))
    (hφ : ∀ (m : normalizer (L : Set G)) (x : TraceZero (ZMod 2)),
      (b.symm (Multiplicative.ofAdd
        (traceZeroAction (ZMod 2) (φ m) x)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹)
    (m : normalizer (L : Set G)) (v : V) :
    (v : G) ∈ centralizer ({(m : G)} : Set G) ↔
      action (ZMod 2) (φ m) (mk (ZMod 2) (b v).toAdd) =
        mk (ZMod 2) (b v).toAdd := by
  constructor
  · intro hc
    rw [action_mk]
    apply congrArg (mk (ZMod 2))
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hφ]
    change (m : G) * (b.symm (b v) : G) * (m : G)⁻¹ = (b.symm (b v) : G)
    rw [b.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc).symm
  · intro hv
    have hf := Extensions.traceZero_fixed_of_natural_fixed (φ m) (b v).toAdd hv
    have he := hφ m (b v).toAdd
    rw [hf] at he
    change (b.symm (b v) : G) =
      (m : G) * (b.symm (b v) : G) * (m : G)⁻¹ at he
    rw [b.symm_apply_apply] at he
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he.symm).symm

omit [Finite G] in
/-- Apply fixed lifting to an actual subgroup of the source normalizer.
The b, φ and conjugation formula are exactly those returned by
`exists_normalizer_full_g2_actor_marked`; no image-surjectivity assumption
or replacement of the original acting subgroup is required. -/
theorem normalizer_actor_centralizes_iff_natural_fixed
    (b : V ≃* Multiplicative (TraceZero (ZMod 2)))
    (φ : normalizer (L : Set G) →* Atlas.G2.Model (ZMod 2))
    (hφ : ∀ (m : normalizer (L : Set G)) (x : TraceZero (ZMod 2)),
      (b.symm (Multiplicative.ofAdd
        (traceZeroAction (ZMod 2) (φ m) x)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹)
    (hAN : A ≤ normalizer (L : Set G)) (hWV : W ≤ V) :
    W ≤ centralizer (A : Set G) ↔
      ∀ (a : A) (w : W),
        action (ZMod 2) (φ (inclusion hAN a))
          (mk (ZMod 2) (b (inclusion hWV w)).toAdd) =
        mk (ZMod 2) (b (inclusion hWV w)).toAdd := by
  constructor
  · intro hc a w
    apply (normalizer_actor_mem_centralizer_iff_natural_fixed b φ hφ
      (inclusion hAN a) (inclusion hWV w)).mp
    exact mem_centralizer_singleton_iff.mpr (hc w.property a a.property).symm
  · intro hf w hw a ha
    have hc := (normalizer_actor_mem_centralizer_iff_natural_fixed b φ hφ
      (inclusion hAN ⟨a, ha⟩) (inclusion hWV ⟨w, hw⟩)).mpr (hf ⟨a, ha⟩ ⟨w, hw⟩)
    exact (mem_centralizer_singleton_iff.mp hc).symm

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
