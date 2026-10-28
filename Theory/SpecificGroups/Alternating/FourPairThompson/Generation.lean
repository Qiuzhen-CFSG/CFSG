module
public import Theory.SpecificGroups.Alternating.FourPairThompson.Elementary
import Mathlib.Tactic
/-!
# Independent odd coordinates generate the full wreath product

The alternating base together with one odd single-coordinate permutation
contains its full S₄ factor. Any factor-exchanging element then gives both
factors and the whole wreath product. All identities use the actual regular
wreath coordinates. This is the generation step in the A₄-pair case of
Aschbacher–Smith 14.1.10, printed p.978.
-/
@[expose] public section
namespace AlternatingFourPair.Thompson
open Subgroup

def axis (i : Q) : D →* W := baseMap.comp (MonoidHom.mulSingle (fun _ : Q => D) i)
@[simp] theorem axis_left (i : Q) (x : D) : (axis i x).left = Pi.mulSingle i x := rfl
@[simp] theorem axis_right (i : Q) (x : D) : (axis i x).right = 1 := rfl

 theorem axis_conj (g : W) (i : Q) (x : D) :
    g * axis i x * g⁻¹ = axis (g.right * i) (g.left (g.right * i) * x * (g.left (g.right * i))⁻¹) := by
  apply RegularWreathProduct.ext
  · funext j
    by_cases h : j = g.right * i
    · subst j; simp [mul_assoc]
    · have h' : g.right⁻¹ * j ≠ i := by
        intro hh
        apply h
        simpa [mul_assoc] using congrArg (fun z => g.right * z) hh
      simp [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h', mul_assoc]
  · simp

 theorem axis_mem_alternatingBase (i : Q) (x : D) (hx : x ∈ alternatingGroup (Fin 4)) :
    axis i x ∈ alternatingBase := by
  refine ⟨rfl, fun j => ?_⟩
  by_cases h : j = i
  · subst j; simpa using hx
  · simp [Pi.mulSingle_eq_of_ne h]

 theorem axis_all_mem_of_odd (H : Subgroup W) (hA : alternatingBase ≤ H)
    (i : Q) (x : D) (hx : axis i x ∈ H) (hxodd : x ∉ alternatingGroup (Fin 4)) :
    ∀ d : D, axis i d ∈ H := by
  intro d
  by_cases hd : d ∈ alternatingGroup (Fin 4)
  · exact hA (axis_mem_alternatingBase i d hd)
  · have he : d * x⁻¹ ∈ alternatingGroup (Fin 4) := by
      rw [(alternatingGroup (Fin 4)).mul_mem_iff_of_index_two alternatingGroup.index_eq_two]
      simp [hd, hxodd]
    have hh := H.mul_mem (hA (axis_mem_alternatingBase i _ he)) hx
    simpa only [← map_mul, inv_mul_cancel_right] using hh

 theorem base_factorization (w : W) (hw : w ∈ base) :
    w = axis 1 (w.left 1) * axis swapIndex (w.left swapIndex) := by
  apply RegularWreathProduct.ext
  · funext i
    rcases index_cases i with rfl | rfl <;> simp
  · simpa using hw

 theorem eq_top_of_axis (H : Subgroup W) (hA : alternatingBase ≤ H)
    (ht : ¬ H ≤ base) (i : Q) (x : D) (hx : axis i x ∈ H)
    (hxodd : x ∉ alternatingGroup (Fin 4)) : H = ⊤ := by
  obtain ⟨t, htH, htB⟩ := Set.not_subset.mp ht
  have htr : t.right = swapIndex := (index_cases _).resolve_left htB
  have hi : ∀ d, axis i d ∈ H := axis_all_mem_of_odd H hA i x hx hxodd
  have hi' : ∀ d, axis (swapIndex * i) d ∈ H := by
    intro d
    have hh := H.mul_mem (H.mul_mem htH (hi ((t.left (t.right * i))⁻¹ * d * t.left (t.right * i))))
      (H.inv_mem htH)
    rw [axis_conj] at hh
    simpa [htr, mul_assoc] using hh
  have hb : base ≤ H := by
    intro w hw
    rw [base_factorization w hw]
    apply H.mul_mem
    · rcases index_cases i with rfl | rfl
      · exact hi _
      · simpa using hi' (w.left 1)
    · rcases index_cases i with rfl | rfl
      · simpa using hi' (w.left swapIndex)
      · exact hi _
  apply top_unique
  intro w _
  rcases index_cases w.right with hw | hw
  · exact hb hw
  · have hwt : w * t⁻¹ ∈ base := by simp [hw, htr]
    simpa using H.mul_mem (hb hwt) htH
end AlternatingFourPair.Thompson
