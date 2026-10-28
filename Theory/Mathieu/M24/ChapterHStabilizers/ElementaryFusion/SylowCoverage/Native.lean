module
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage.Checks

/-!
# Native interpretation of vertices and candidate words

The vertex list contains every square-one native Sylow element. Native
commutation implies compatibility in the checked graph. The five-generator
candidates have exhaustive 32-word lists, obtained by toggling generator bits;
this proves their order bounds and interprets all six terminal masks.
Source: Aschbacher–Smith H.14.1(1,5), printed pp.396–397.
-/
@[expose] public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open M24LocalGeometry SylowNormalizer.OrderEnumeration

noncomputable def native (v : Fin 192) : SylowNormalizer.candidate := element (vertexIndex v)

theorem native_apply (v : Fin 192) (x : Fin 24) :
    (native v).val.val x = vertexPoint v x := by
  rw [vertexPoint_spec]
  exact element_apply _ _

theorem vertex_of_square (g : SylowNormalizer.candidate) (hg : g ^ 2 = 1) :
    ∃ v, native v = g := by
  obtain ⟨i, rfl⟩ := element_surjective g
  have hs (x : Fin 24) : point i (point i x) = x := by
    have h := congrArg (fun a : SylowNormalizer.candidate => a.val.val x) hg
    simpa only [pow_two, Subgroup.coe_mul, Equiv.Perm.mul_apply, element_apply,
      Subgroup.coe_one, Equiv.Perm.one_apply] using h
  rcases square_rejection i with h | h | h | h
  · exact ⟨vertexCode i, congrArg element h⟩
  · exact (h (hs 0)).elim
  · exact (h (hs 1)).elim
  · exact (h (hs 5)).elim

theorem native_compatible (v w : Fin 192) (h : native v * native w = native w * native v) :
    compatible v w = true := by
  have hp (x : Fin 24) :
      vertexPoint v (vertexPoint w x) = vertexPoint w (vertexPoint v x) := by
    have h' := congrArg (fun a : SylowNormalizer.candidate => a.val.val x) h
    simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, native_apply] using h'
  exact compatible_check v w ⟨hp 0, hp 1, hp 5⟩

theorem native_generator (k : Fin 4) (a : Fin 5) :
    native (generatorVertex k a) = element (smallGeneratorIndex k a) := by
  rw [native, generatorVertex_spec]

theorem small_step (k : Fin 4) (a : Fin 5) (j : Fin 32) :
    element (smallGeneratorIndex k a) * native (smallRow k j) =
      native (smallRow k (toggle a j)) := by
  apply EvenCatalogue.NormalizerOvergroupsProof.candidate_ext
  intro b
  rw [← native_generator]
  change (native (generatorVertex k a)).val.val
    ((native (smallRow k j)).val.val _) = _
  simp only [native_apply]
  exact small_step_check k a j b

theorem small_generator_inv (k : Fin 4) (a : Fin 5) :
    (smallGenerator k a)⁻¹ = smallGenerator k a := by
  have h : element (smallGeneratorIndex k a) * element (smallGeneratorIndex k a) = 1 := by
    apply EvenCatalogue.NormalizerOvergroupsProof.candidate_ext
    intro b
    rw [← native_generator]
    change (native (generatorVertex k a)).val.val
      ((native (generatorVertex k a)).val.val _) = _
    simp only [native_apply]
    exact small_square_check k a b
  apply inv_eq_of_mul_eq_one_right
  exact congrArg Subtype.val h

theorem small_row_zero (k : Fin 4) : native (smallRow k 0) = 1 := by
  rw [native, small_zero_check, EvenCatalogue.Coverage.element_zero]

theorem small_row_mem (k : Fin 4) (j : Fin 32) :
    (native (smallRow k j)).val ∈ smallCandidate k := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    by_cases hj : j = 0
    · subst j
      rw [small_row_zero]
      exact (smallCandidate k).one_mem
    · obtain ⟨hlt, he⟩ := lower_check j hj
      have hm := (smallCandidate k).mul_mem (smallGenerator_mem k (lastBit j))
        (ih (lowerMask j) hlt)
      change (element (smallGeneratorIndex k (lastBit j)) *
        native (smallRow k (lowerMask j))).val ∈ smallCandidate k at hm
      rw [small_step, he] at hm
      exact hm

theorem mem_smallCandidate_iff (k : Fin 4) (g : M24) :
    g ∈ smallCandidate k ↔ ∃ j : Fin 32, (native (smallRow k j)).val = g := by
  constructor
  · intro hg
    apply Subgroup.closure_induction_left (s := Set.range (smallGenerator k))
      (p := fun g _ => ∃ j : Fin 32, (native (smallRow k j)).val = g) ?_ ?_ ?_ hg
    · exact ⟨0, congrArg Subtype.val (small_row_zero k)⟩
    · rintro _ ⟨a, rfl⟩ _ _ ⟨j, rfl⟩
      exact ⟨toggle a j, (congrArg Subtype.val (small_step k a j)).symm⟩
    · rintro _ ⟨a, rfl⟩ _ _ ⟨j, rfl⟩
      rw [small_generator_inv]
      exact ⟨toggle a j, (congrArg Subtype.val (small_step k a j)).symm⟩
  · rintro ⟨j, rfl⟩
    exact small_row_mem k j

theorem smallCandidate_card_le (k : Fin 4) : Nat.card (smallCandidate k) ≤ 32 := by
  let f : Fin 32 → smallCandidate k := fun j =>
    ⟨(native (smallRow k j)).val, small_row_mem k j⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨j, hj⟩ := (mem_smallCandidate_iff k g.val).mp g.property
    exact ⟨j, Subtype.ext hj⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf

theorem small_mask_mem (k : Fin 4) (v : Fin 192)
    (h : (largeMask k.castSucc.castSucc).testBit v.val = true) :
    (native v).val ∈ smallCandidate k := by
  have he := congrArg (fun i => (element i).val) (small_mask_check k v h)
  exact he.symm ▸ small_row_mem k ⟨(wordCode k.castSucc.castSucc v).val % 32,
    Nat.mod_lt _ (by decide)⟩

theorem even_mask_mem (k : Fin 2) (v : Fin 192)
    (h : (largeMask ⟨4 + k.val, by omega⟩).testBit v.val = true) :
    (native v).val ∈ EvenCandidates.elementary k := by
  have he := congrArg (fun i => (element i).val) (even_mask_check k v h)
  have hm := EvenCatalogue.NormalizerOvergroupsProof.rowElement_mem
    (if k = 0 then 20 else 21) (wordCode ⟨4 + k.val, by omega⟩ v)
  rw [EvenCatalogue.NormalizerOvergroupsProof.last_ambient] at hm
  exact he.symm ▸ hm

noncomputable def largeCandidate : Fin 6 → Subgroup M24 :=
  ![smallCandidate 0, smallCandidate 1, smallCandidate 2, smallCandidate 3,
    EvenCandidates.elementary 0, EvenCandidates.elementary 1]

theorem large_mask_mem (k : Fin 6) (v : Fin 192)
    (h : (largeMask k).testBit v.val = true) : (native v).val ∈ largeCandidate k := by
  fin_cases k
  · exact small_mask_mem 0 v h
  · exact small_mask_mem 1 v h
  · exact small_mask_mem 2 v h
  · exact small_mask_mem 3 v h
  · exact even_mask_mem 0 v h
  · exact even_mask_mem 1 v h

end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
