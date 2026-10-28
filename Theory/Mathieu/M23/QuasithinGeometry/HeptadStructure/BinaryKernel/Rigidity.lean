module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic

/-!
# Rigidity of the pointwise heptad stabilizer

Eight certified heptads through a complementary point separate all sixteen
complementary points. Each has three points in the distinguished heptad, so
unique four-point extension makes it invariant under a permutation fixing the
heptad and that complementary point. This proves evaluation injectivity and
bounds the pointwise kernel by sixteen, independently of its quotient action.

The incidence tables are extracted from the existing `m23BlockMaskArray` and
checked by the Lean kernel. Source: Aschbacher, *Sporadic Groups*, Chapter 6,
Lemma 19.1, specialized to M23; Aschbacher--Smith, §5.2, printed p.655.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

private def separatingIndex : Fin 23 → Fin 8 → Fin 253 :=
  ![![4, 8, 55, 56, 9, 30, 32, 19],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 5, 49, 50, 9, 29, 30, 13],
    ![2, 6, 51, 52, 9, 31, 32, 15],
    ![3, 7, 53, 54, 9, 29, 31, 17],
    ![1, 8, 49, 55, 10, 32, 33, 15],
    ![4, 5, 50, 56, 10, 29, 33, 16],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 7, 51, 54, 10, 29, 36, 14],
    ![3, 5, 49, 54, 11, 30, 34, 15],
    ![1, 6, 53, 55, 12, 35, 36, 18],
    ![2, 8, 52, 56, 11, 30, 35, 13],
    ![4, 7, 50, 51, 12, 34, 36, 13],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![3, 6, 52, 53, 10, 32, 36, 13],
    ![1, 7, 50, 53, 11, 31, 34, 16],
    ![2, 5, 54, 56, 12, 33, 34, 17],
    ![3, 8, 49, 52, 12, 33, 35, 14],
    ![4, 6, 51, 55, 11, 31, 35, 14]]

private noncomputable def separatingBlock (a : Fin 23) (i : Fin 8) :=
  m23BlockAt (separatingIndex a i)

private theorem separatingBlock_four : ∀ a : Fin 23, a ∉ omega → ∀ i : Fin 8,
    (insert a (omega ∩ separatingBlock a i)).card = 4 ∧
      insert a (omega ∩ separatingBlock a i) ⊆ separatingBlock a i := by
  decide +kernel

private theorem separatingBlock_separates : ∀ a : Fin 23, a ∉ omega →
    ∀ b c : Fin 23, b ∉ omega → c ∉ omega →
    (∀ i : Fin 8, b ∈ separatingBlock a i ↔ c ∈ separatingBlock a i) → b = c := by
  decide +kernel

private theorem separatingBlock_mem (a : Fin 23) (i : Fin 8) :
    separatingBlock a i ∈ m23Blocks := by
  exact Finset.mem_image.mpr ⟨separatingIndex a i, Finset.mem_univ _, rfl⟩

/-- An M23 permutation fixing the heptad and one point outside it is the identity. -/
theorem heptad_fixer_eq_one_of_fix_complement (g : M23)
    (hg : ∀ b ∈ omega, g • b = b) (a : Fin 23) (ha : a ∉ omega)
    (hga : g • a = a) : g = 1 := by
  have hblock (i : Fin 8) : g • separatingBlock a i = separatingBlock a i := by
    obtain ⟨hc, hs⟩ := separatingBlock_four a ha i
    apply heptad_eq_of_four_subset hc (smul_heptad g (separatingBlock_mem a i))
      (separatingBlock_mem a i) _ hs
    intro b hb
    have hbfix : g • b = b := by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hga
      · exact hg b (Finset.mem_inter.mp hb).1
    rw [← hbfix]
    exact Finset.smul_mem_smul_finset (hs hb)
  apply Subtype.ext
  apply Equiv.ext
  intro b
  change g • b = b
  by_cases hb : b ∈ omega
  · exact hg b hb
  · have hgb : g • b ∉ omega := by
      intro h
      have hh := hg (g • b) h
      exact hb ((MulAction.injective g) hh ▸ h)
    apply separatingBlock_separates a ha (g • b) b hgb hb
    intro i
    simpa only [hblock i] using
      (Finset.smul_mem_smul_finset_iff (s := separatingBlock a i) (b := b) g)

/-- Evaluating a pointwise heptad fixer at any complementary point is injective. -/
theorem heptadKernel_eval_injective (a : Fin 23) (ha : a ∉ omega) :
    Function.Injective (fun g : heptadKernel => ((g : heptadStabilizer) : M23) • a) := by
  intro g h hgh
  change ((g : heptadStabilizer) : M23) • a = ((h : heptadStabilizer) : M23) • a at hgh
  have ht : g⁻¹ * h = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply heptad_fixer_eq_one_of_fix_complement
    · exact (mem_heptadKernel _).mp (g⁻¹ * h).property
    · exact ha
    · change (((g : heptadStabilizer) : M23)⁻¹ *
        ((h : heptadStabilizer) : M23)) • a = a
      rw [mul_smul, ← hgh, inv_smul_smul]
  exact inv_mul_eq_one.mp ht

/-- The complement is invariant under every pointwise heptad fixer. -/
theorem heptadKernel_smul_mem_complement (g : heptadKernel)
    {a : Fin 23} (ha : a ∈ pairComplement omega) :
    ((g : heptadStabilizer) : M23) • a ∈ pairComplement omega := by
  simp only [pairComplement, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
  intro h
  have hf := (mem_heptadKernel _).mp g.property _ h
  exact ha ((MulAction.injective ((g : heptadStabilizer) : M23)) hf ▸ h)

/-- Evaluation, with its natural sixteen-point codomain. -/
noncomputable def heptadKernelEvaluation (a : pairComplement omega) :
    heptadKernel → pairComplement omega :=
  fun g => ⟨((g : heptadStabilizer) : M23) • a.val,
    heptadKernel_smul_mem_complement g a.property⟩

theorem heptadKernelEvaluation_injective (a : pairComplement omega) :
    Function.Injective (heptadKernelEvaluation a) := by
  intro g h heq
  exact heptadKernel_eval_injective a.val (Finset.mem_sdiff.mp a.property).2
    (congrArg Subtype.val heq)

theorem heptadComplement_card : (pairComplement omega).card = 16 := by decide +kernel

/-- The design alone bounds the pointwise kernel, without a quotient identification. -/
theorem heptadKernel_card_le : Nat.card heptadKernel ≤ 16 := by
  let a : pairComplement omega := ⟨0, by decide +kernel⟩
  have hc := Nat.card_le_card_of_injective _ (heptadKernelEvaluation_injective a)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, heptadComplement_card] using hc

end Sporadic.Mathieu.M23Geometry
