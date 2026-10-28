module
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation

/-!
# Orbit preservation in the binary six-letter augmentation core

The two nonconstant A₆ orbits both contain fifteen words, so orbit sizes
alone do not distinguish them. Within each orbit, join x to y when x+y
also lies in that orbit. The weight-two orbit has degree eight, whereas
the weight-four orbit has degree six. An additive orbit permutation
preserves these degrees, and therefore preserves each individual orbit.
The finite certificate checks only the 32 core vectors and their sums.

This supplies the normality reduction in Aschbacher--Smith, combined
manuscript (1 March 2004), Lemma 12.6.11, printed p.825, without requiring
a classification of the full linear normalizer.
-/

public noncomputable section
namespace BinaryPermutation
local instance sixOrbitDecidableMem : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance sixOrbitFintype : Fintype (core (Fin 6)) := Subtype.fintype _

private def degree (v : core (Fin 6)) : ℕ :=
  (Finset.univ.filter fun w : core (Fin 6) =>
    wordWeight w.val = wordWeight v.val ∧
      wordWeight (v + w).val = wordWeight v.val).card

private theorem degree_table (v : core (Fin 6)) :
    (wordWeight v.val = 0 ∧ degree v = 1) ∨
    (wordWeight v.val = 2 ∧ degree v = 8) ∨
    (wordWeight v.val = 4 ∧ degree v = 6) ∨
    (wordWeight v.val = 6 ∧ degree v = 0) := by
  revert v
  decide +kernel

private theorem degree_ncard (v : core (Fin 6)) : degree v =
    {w : core (Fin 6) | wordWeight w.val = wordWeight v.val ∧
      wordWeight (v + w).val = wordWeight v.val}.ncard := by
  rw [show {w : core (Fin 6) | wordWeight w.val = wordWeight v.val ∧
      wordWeight (v + w).val = wordWeight v.val} =
    ↑(Finset.univ.filter fun w : core (Fin 6) =>
      wordWeight w.val = wordWeight v.val ∧
        wordWeight (v + w).val = wordWeight v.val) by ext; simp,
    Set.ncard_coe_finset]
  rfl

theorem six_core_orbit_preserved
    (e : core (Fin 6) ≃+ core (Fin 6))
    (he : ∀ x : core (Fin 6),
      e '' (Set.range fun a : alternatingGroup (Fin 6) =>
        alternatingCoreRepresentation (Fin 6) a x) =
      Set.range fun a : alternatingGroup (Fin 6) =>
        alternatingCoreRepresentation (Fin 6) a (e x))
    (v : core (Fin 6)) :
    ∃ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a v = e v := by
  have he' (x : core (Fin 6)) :
      e '' {y : core (Fin 6) | wordWeight y.val = wordWeight x.val} =
        {y : core (Fin 6) | wordWeight y.val = wordWeight (e x).val} := by
    simpa only [even_core_orbit_eq_weight (by decide : 3 ≤ Fintype.card (Fin 6))] using he x
  have hw (x y : core (Fin 6)) :
      wordWeight (e y).val = wordWeight (e x).val ↔
        wordWeight y.val = wordWeight x.val := by
    change e y ∈ {z : core (Fin 6) | wordWeight z.val = wordWeight (e x).val} ↔ _
    rw [← he', Set.mem_image]
    constructor
    · rintro ⟨z,hz,hzy⟩
      exact e.injective hzy ▸ hz
    · intro hy
      exact ⟨y,hy,rfl⟩
  have himage : e '' {w : core (Fin 6) | wordWeight w.val = wordWeight v.val ∧
      wordWeight (v + w).val = wordWeight v.val} =
    {w : core (Fin 6) | wordWeight w.val = wordWeight (e v).val ∧
      wordWeight (e v + w).val = wordWeight (e v).val} := by
    ext w
    obtain ⟨w,rfl⟩ := e.surjective w
    rw [Set.mem_image]
    constructor
    · rintro ⟨u,hu,huu⟩
      have hh : u = w := e.injective huu
      subst u
      exact ⟨(hw v w).mpr hu.1, by rw [← map_add]; exact (hw v (v+w)).mpr hu.2⟩
    · rintro ⟨h₁,h₂⟩
      refine ⟨w,⟨(hw v w).mp h₁,?_⟩,rfl⟩
      rw [← map_add] at h₂
      exact (hw v (v+w)).mp h₂
  have hd : degree v = degree (e v) := by
    rw [degree_ncard,degree_ncard,←himage,Set.ncard_image_of_injective _ e.injective]
  have hweight : wordWeight (e v).val = wordWeight v.val := by
    have hv := degree_table v
    have hev := degree_table (e v)
    omega
  rw [← Set.mem_range,even_core_orbit_eq_weight (by decide)]
  exact hweight
end BinaryPermutation
