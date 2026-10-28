module
public import Theory.Representation.SixLetterRadicalDisplacement
import Mathlib.Tactic
/-!
# The point section of the binary six-letter augmentation cover

The constant line and the weight-four plane span the vectors constant on
three coordinate pairs. A cyclic permutation of these pairs acts irreducibly
on the two-dimensional quotient: any vector outside that space and its cyclic
translate generate the quotient. The weight-four plane also determines its
partition stabilizer. These facts retain the constant line of the cover.

Source: Aschbacher--Smith, proof of 13.8.33, printed p.967, and the
six-letter flag geometry in B.3.4. The original subgroup application is in
Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverPoint.
-/

@[expose] public section
open Subgroup Representation BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace Representation.SixLetterCoverPoint
open SixLetterRadicalDisplacement
private local instance : DecidablePred (fun v : Fin 6 → ZMod 2 => v ∈ core (Fin 6)) :=
  fun v => inferInstanceAs (Decidable (augmentation (Fin 6) v = 0))
private local instance : Fintype U :=
  Fintype.ofFinset (Finset.univ.filter (fun v => v ∈ core (Fin 6))) (by simp)
/-- Cyclic permutation of the three coordinate pairs. -/
def pairCycle : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)
theorem pairCycle_mem : pairCycle ∈ H2 := by decide
/-- Coordinates constant on each of the three pairs. -/
def pairSpace : Submodule (ZMod 2) U where
  carrier := {v | v.val 0 = v.val 1 ∧ v.val 2 = v.val 3 ∧ v.val 4 = v.val 5}
  zero_mem' := ⟨rfl,rfl,rfl⟩
  add_mem' hv hw := ⟨congrArg₂ (·+·) hv.1 hw.1,
    congrArg₂ (·+·) hv.2.1 hw.2.1,congrArg₂ (·+·) hv.2.2 hw.2.2⟩
  smul_mem' c _ hv := ⟨congrArg (c * ·) hv.1,
    congrArg (c * ·) hv.2.1,congrArg (c * ·) hv.2.2⟩
private local instance (v : U) : Decidable (v ∈ pairSpace) :=
  inferInstanceAs (Decidable (v.val 0 = v.val 1 ∧ v.val 2 = v.val 3 ∧ v.val 4 = v.val 5))
theorem pairSpace_eq : pairSpace = F ⊔ W := by
  rw [F_sup_W_eq_pairSpan]
  apply le_antisymm
  · intro v hv
    have hd : ∀ v : U, v ∈ pairSpace →
        v = v.val 0 • q 0 1 + v.val 2 • q 2 3 + v.val 4 • q 4 5 := by decide +kernel
    rw [hd v hv]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    rintro v (rfl | rfl | rfl) <;> change _ = _ ∧ _ = _ ∧ _ = _ <;> decide
private def weightPlane : Submodule (ZMod 2) U :=
  pairSpace ⊓ LinearMap.ker
    (((LinearMap.proj (0 : Fin 6) : (Fin 6 → ZMod 2) →ₗ[ZMod 2] ZMod 2) + LinearMap.proj (2 : Fin 6) + LinearMap.proj (4 : Fin 6)).comp
      (core (Fin 6)).subtype)
private local instance (v : U) : Decidable (v ∈ weightPlane) :=
  inferInstanceAs (Decidable ((v.val 0 = v.val 1 ∧ v.val 2 = v.val 3 ∧ v.val 4 = v.val 5) ∧
    v.val 0 + v.val 2 + v.val 4 = 0))
private theorem weightPlane_eq : weightPlane = W := by
  apply le_antisymm
  · intro v hv
    have hd : ∀ v : U, v ∈ weightPlane →
        v = v.val 2 • (q 0 1 + q 2 3) + v.val 4 • (q 0 1 + q 4 5) := by decide +kernel
    rw [hd v hv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    rintro v (rfl | rfl) <;>
      change (_ = _ ∧ _ = _ ∧ _ = _) ∧ _ = _ <;> decide
/-- Preserving the weight-four plane preserves the partition into three pairs. -/
theorem weight_plane_stabilizer (g : Equiv.Perm (Fin 6))
    (hg : ∀ v ∈ W, coreRepresentation (Fin 6) g v ∈ W) : g ∈ H2 := by
  have cert : ∀ g : Equiv.Perm (Fin 6),
      coreRepresentation (Fin 6) g (q 0 1 + q 2 3) ∈ weightPlane →
      coreRepresentation (Fin 6) g (q 0 1 + q 4 5) ∈ weightPlane → g ∈ H2 := by decide +kernel
  apply cert g
  · rw [weightPlane_eq]
    exact hg _ (Submodule.subset_span (by simp))
  · rw [weightPlane_eq]
    exact hg _ (Submodule.subset_span (by simp))
private theorem orbit_spans : ∀ v : U, v ∉ pairSpace → ∀ w : U,
    ∃ a b : ZMod 2, w - a • v - b • coreRepresentation (Fin 6) pairCycle v ∈ pairSpace := by
  decide +kernel
/-- Every invariant subspace above the pair space is either that space or the whole cover. -/
theorem invariant_dichotomy (S : Submodule (ZMod 2) U)
    (hC : F ⊔ W ≤ S)
    (hS : ∀ v ∈ S, coreRepresentation (Fin 6) pairCycle v ∈ S) :
    S = F ⊔ W ∨ S = ⊤ := by
  by_cases he : S ≤ F ⊔ W
  · exact Or.inl (le_antisymm he hC)
  right
  obtain ⟨v,hv,hvC⟩ := SetLike.not_le_iff_exists.mp he
  apply top_unique
  intro w _
  obtain ⟨a,b,hab⟩ := orbit_spans v (by simpa [pairSpace_eq] using hvC) w
  have hm := S.add_mem (S.add_mem (hC (pairSpace_eq ▸ hab)) (S.smul_mem b (hS v hv)))
    (S.smul_mem a hv)
  simpa only [sub_add_cancel] using hm
end Representation.SixLetterCoverPoint
