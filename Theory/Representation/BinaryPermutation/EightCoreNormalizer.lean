module
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation

/-!
# Normalizers preserve the weight-two orbit in the binary A₈ core

An additive automorphism permuting the actual A₈ orbits preserves weight two.
The only orbits of size 28 have weights two and six. The former contains an
additive triangle, whereas the sum of two weight-six words has weight at most
four. Thus an additive orbit permutation cannot exchange these two orbits.

This uses the seven-dimensional augmentation core, without passing to its
six-dimensional constant-line quotient. The finite certificates enumerate
only the 128 core words and the 256 full words, never the permutation group.

Source: Aschbacher--Smith, 12.2.16, printed p.800, the point-Sylow supplement
T = C_T(v)(T ∩ L). The actual source action is applied in
FusionEightGeometryModuleSupplement.
-/

public noncomputable section
namespace BinaryPermutation
local instance eightCoreNormalizerDecidable : DecidablePred (· ∈ core (Fin 8)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance eightCoreNormalizerFintype : Fintype (core (Fin 8)) := Subtype.fintype _

private theorem eight_weights (v : core (Fin 8)) :
    wordWeight v.val = 0 ∨ wordWeight v.val = 2 ∨ wordWeight v.val = 4 ∨
      wordWeight v.val = 6 ∨ wordWeight v.val = 8 := by
  revert v
  decide +kernel

private theorem eight_counts :
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 0).card = 1 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 2).card = 28 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 4).card = 70 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 6).card = 28 ∧
    (Finset.univ.filter fun v : core (Fin 8) => wordWeight v.val = 8).card = 1 := by
  decide +kernel

private theorem weight_complement (v : Full (Fin 8)) :
    wordWeight (v + allOne (Fin 8)) + wordWeight v = 8 := by
  revert v
  decide +kernel

private theorem weight_add_le {Ω : Type*} [Fintype Ω] (v w : Full Ω) :
    wordWeight (v + w) ≤ wordWeight v + wordWeight w := by
  classical
  apply (Finset.card_le_card (show
    (Finset.univ.filter fun i => (v + w) i ≠ 0) ⊆
      (Finset.univ.filter fun i => v i ≠ 0) ∪
        (Finset.univ.filter fun i => w i ≠ 0) from ?_)).trans
      (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra hn
  push Not at hn
  exact hi (by simp [Pi.add_apply, hn.1, hn.2])

private theorem weight_six_add_ne_six (v w : Full (Fin 8))
    (hv : wordWeight v = 6) (hw : wordWeight w = 6) :
    wordWeight (v + w) ≠ 6 := by
  have hv' := weight_complement v
  have hw' := weight_complement w
  have hb := weight_add_le (v + allOne (Fin 8)) (w + allOne (Fin 8))
  have he : (v + allOne (Fin 8)) + (w + allOne (Fin 8)) = v + w := by
    ext i
    change (v i + 1) + (w i + 1) = v i + w i
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    linear_combination htwo
  rw [he] at hb
  omega

private def triangleA : core (Fin 8) := ⟨![1,1,0,0,0,0,0,0], by rw [mem_core]; decide⟩
private def triangleB : core (Fin 8) := ⟨![1,0,1,0,0,0,0,0], by rw [mem_core]; decide⟩

/-- An additive automorphism that permutes the actual A₈ core orbits preserves
weight two. The equal-sized weight-six orbit has no additive triangle. -/
theorem eight_core_weight_two_of_orbit_image
    (e : core (Fin 8) ≃+ core (Fin 8))
    (he : ∀ x : core (Fin 8),
      e '' (Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) a x) =
      Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) a (e x))
    (v : core (Fin 8)) (hv : wordWeight v.val = 2) :
    wordWeight (e v).val = 2 := by
  have he' (x : core (Fin 8)) :
      e '' {y : core (Fin 8) | wordWeight y.val = wordWeight x.val} =
        {y : core (Fin 8) | wordWeight y.val = wordWeight (e x).val} := by
    simpa only [even_core_orbit_eq_weight (by decide : 3 ≤ Fintype.card (Fin 8))] using he x
  have hsame (x y : core (Fin 8)) (hxy : wordWeight x.val = wordWeight y.val) :
      wordWeight (e x).val = wordWeight (e y).val := by
    have hx : e x ∈ e '' {z : core (Fin 8) | wordWeight z.val = wordWeight y.val} :=
      ⟨x, hxy, rfl⟩
    rwa [he'] at hx
  have hcount (x : core (Fin 8)) :
      {y : core (Fin 8) | wordWeight y.val = wordWeight x.val}.ncard =
        (Finset.univ.filter fun y : core (Fin 8) =>
          wordWeight y.val = wordWeight x.val).card := by
    rw [show {y : core (Fin 8) | wordWeight y.val = wordWeight x.val} =
      ↑(Finset.univ.filter fun y : core (Fin 8) =>
        wordWeight y.val = wordWeight x.val) by ext; simp, Set.ncard_coe_finset]
  have hc := congrArg Set.ncard (he' v)
  rw [Set.ncard_image_of_injective _ e.injective, hcount, hcount, hv,
    eight_counts.2.1] at hc
  have h26 : wordWeight (e v).val = 2 ∨ wordWeight (e v).val = 6 := by
    rcases eight_weights (e v) with h | h | h | h | h
    · rw [h, eight_counts.1] at hc; contradiction
    · exact Or.inl h
    · rw [h, eight_counts.2.2.1] at hc; contradiction
    · exact Or.inr h
    · rw [h, eight_counts.2.2.2.2] at hc; contradiction
  rcases h26 with h | h
  · exact h
  have ha : wordWeight (e triangleA).val = 6 :=
    (hsame triangleA v (by rw [hv]; decide)).trans h
  have hb : wordWeight (e triangleB).val = 6 :=
    (hsame triangleB v (by rw [hv]; decide)).trans h
  have hab : wordWeight (e (triangleA + triangleB)).val = 6 :=
    (hsame (triangleA + triangleB) v (by rw [hv]; decide)).trans h
  rw [map_add] at hab
  exact (weight_six_add_ne_six (e triangleA).val (e triangleB).val ha hb hab).elim
end BinaryPermutation
