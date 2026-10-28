module

public import Theory.Mathieu.M22.Properties.PairCoreIncidence
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Elementary abelianity of the native pair two-core

Four certified even design automorphisms fix all five hexads through {1,2}.
They are commuting involutions; their sixteen binary products are distinct,
as witnessed by their actions on points 3 and 4. Their closure is therefore
an elementary subgroup of order at least sixteen inside the already counted
pair two-core of order sixteen. Equality proves the native E₁₆ assertion.
Conjugation gives the same result for the pair {0,4}.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. The certificates
use the repository's degree-22 ATLAS generators; discovery and reproduction
are documented in `source/README.md`. All finite assertions are checked by
the Lean kernel. No external computation is used as a proof oracle.
-/

public section
open Subgroup Sporadic.Mathieu MulAction Theory.GroupTheory
open Sporadic.Mathieu.M22ValueBound.Concrete
open scoped Pointwise
namespace Sporadic.Mathieu

private def generator : Fin 4 → Equiv.Perm (Fin 22) := ![
  Equiv.swap 4 15 * Equiv.swap 5 6 * Equiv.swap 7 21 * Equiv.swap 8 17 * Equiv.swap 9 0 * Equiv.swap 11 13 * Equiv.swap 12 16 * Equiv.swap 14 19,
  Equiv.swap 4 21 * Equiv.swap 5 14 * Equiv.swap 6 19 * Equiv.swap 7 15 * Equiv.swap 8 0 * Equiv.swap 9 17 * Equiv.swap 11 16 * Equiv.swap 12 13,
  Equiv.swap 3 20 * Equiv.swap 5 6 * Equiv.swap 8 0 * Equiv.swap 9 17 * Equiv.swap 10 18 * Equiv.swap 11 12 * Equiv.swap 13 16 * Equiv.swap 14 19,
  Equiv.swap 3 10 * Equiv.swap 5 19 * Equiv.swap 6 14 * Equiv.swap 8 17 * Equiv.swap 9 0 * Equiv.swap 11 16 * Equiv.swap 12 13 * Equiv.swap 18 20]

private def blockIndexArray : Fin 4 → Array (Fin 77) := ![
  #[
    0, 1, 2, 3, 4, 8, 7, 6, 5, 15, 13, 19, 14, 10, 12, 9, 20,
    18, 17, 11, 16, 22, 21, 24, 23, 32, 35, 34, 31, 30, 29, 28, 25, 36,
    27, 26, 33, 42, 44, 39, 40, 43, 37, 41, 38, 45, 48, 47, 46, 58, 52,
    64, 50, 74, 75, 69, 56, 71, 49, 59, 65, 67, 66, 68, 51, 60, 62, 61,
    63, 55, 70, 57, 76, 73, 53, 54, 72],
  #[
    0, 1, 2, 3, 4, 6, 5, 8, 7, 20, 18, 14, 19, 17, 11, 16, 15,
    13, 10, 12, 9, 24, 23, 22, 21, 36, 29, 31, 34, 26, 35, 27, 33, 32,
    28, 30, 25, 42, 38, 45, 47, 41, 37, 43, 44, 39, 48, 40, 46, 57, 60,
    64, 65, 75, 74, 55, 70, 49, 71, 73, 50, 66, 67, 63, 51, 52, 61, 62,
    68, 69, 56, 58, 76, 59, 54, 53, 72],
  #[
    0, 1, 2, 3, 4, 11, 14, 12, 19, 10, 9, 5, 7, 15, 6, 13, 17,
    16, 20, 8, 18, 25, 32, 33, 36, 21, 27, 26, 30, 31, 28, 29, 22, 23,
    35, 34, 24, 51, 38, 56, 59, 43, 64, 41, 44, 70, 76, 73, 72, 49, 52,
    37, 50, 54, 53, 55, 39, 57, 58, 40, 65, 66, 67, 68, 42, 60, 61, 62,
    63, 69, 45, 71, 48, 47, 75, 74, 46],
  #[
    0, 1, 2, 3, 4, 10, 18, 17, 13, 11, 5, 9, 16, 8, 20, 19, 12,
    7, 6, 15, 14, 26, 35, 30, 29, 27, 21, 25, 33, 24, 23, 36, 34, 28,
    32, 22, 31, 37, 55, 56, 73, 68, 42, 63, 69, 70, 48, 59, 46, 57, 52,
    51, 50, 53, 54, 38, 39, 49, 71, 47, 65, 62, 61, 43, 64, 60, 67, 66,
    41, 44, 45, 58, 76, 40, 74, 75, 72]]

private def blockIndex (j : Fin 4) (i : Fin 77) : Fin 77 :=
  (blockIndexArray j)[i.val]'(by fin_cases j <;> exact i.isLt)

private theorem generator_mem (j : Fin 4) : generator j ∈ M22 := by
  constructor
  · change _ ∈ m22WittDesign.aut
    rw [SteinerSystem.mem_aut_iff]
    have he : generator j • m22Blocks = m22Blocks :=
      m22_blocks_smul_of_index (generator j) (blockIndex j)
        (by revert j; decide +kernel) (fun i => m22Perm_smul_blockAt_of_bits _ _ _ (by
          have hb : ∀ j : Fin 4, ∀ i : Fin 77, ∀ x : Fin 22,
              (m22BlockMask i).testBit ((generator j).symm x).val =
                (m22BlockMask (blockIndex j i)).testBit x.val := by decide +kernel
          exact hb j i))
    have hs := congrArg (fun s : Finset (Finset (Fin 22)) => (s : Set (Finset (Fin 22)))) he
    simpa only [m22WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
      Finset.coe_smul_finset] using hs
  · change generator j ∈ alternatingGroup (Fin 22)
    rw [Equiv.Perm.mem_alternatingGroup]
    fin_cases j <;> simp [generator, Equiv.Perm.sign_swap']

private noncomputable def generatorFirst (j : Fin 4) : first :=
  ⟨⟨generator j, generator_mem j⟩, by
    change generator j • m22Pair12 = m22Pair12
    revert j
    decide +kernel⟩

private theorem generator_core (j : Fin 4) : generatorFirst j ∈ pCore 2 first := by
  rw [← pairAction_ker_eq_twoCore]
  change pairAction (generatorFirst j) = 1
  apply Equiv.ext
  intro i
  apply pairHexad_injective
  rw [pairAction_spec]
  change generator j • pairHexad i = pairHexad i
  have h : ∀ j : Fin 4, ∀ i : Fin 5, generator j • pairHexad i = pairHexad i := by
    decide +kernel
  exact h j i

private def wordPerm (i : Fin 16) : Equiv.Perm (Fin 22) :=
  generator 0 ^ (i.val % 2) * generator 1 ^ (i.val / 2 % 2) *
    generator 2 ^ (i.val / 4 % 2) * generator 3 ^ (i.val / 8 % 2)

private noncomputable def word (i : Fin 16) : first :=
  generatorFirst 0 ^ (i.val % 2) * generatorFirst 1 ^ (i.val / 2 % 2) *
    generatorFirst 2 ^ (i.val / 4 % 2) * generatorFirst 3 ^ (i.val / 8 % 2)

private theorem word_injective : Function.Injective word := by
  have h : ∀ i j : Fin 16, wordPerm i 3 = wordPerm j 3 →
      wordPerm i 4 = wordPerm j 4 → i = j := by decide +kernel
  intro i j hij
  exact h i j (congrArg (fun g : first => g.val.val 3) hij)
    (congrArg (fun g : first => g.val.val 4) hij)

/-- The native pair two-core is genuinely elementary abelian. -/
theorem m22Pair_twoCore_elementary : IsElementaryAbelian 2 (pCore 2 first) := by
  let E := closure (Set.range generatorFirst)
  have hle : E ≤ pCore 2 first := (closure_le _).mpr (by
    rintro _ ⟨j, rfl⟩
    exact generator_core j)
  have hc : ∀ i j, generator i * generator j = generator j * generator i := by
    decide +kernel
  let : IsMulCommutative E := isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Subtype.ext (Subtype.ext (hc i j)))
  have hE : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.closure_of_isMulCommutative _ (by
      rintro _ ⟨i, rfl⟩
      have h : ∀ i, generator i ^ 2 = 1 := by decide +kernel
      exact Subtype.ext (Subtype.ext (h i)))
  have hw (i : Fin 16) : word i ∈ E := by
    have hg (j : Fin 4) : generatorFirst j ∈ E := subset_closure ⟨j, rfl⟩
    exact E.mul_mem (E.mul_mem (E.mul_mem (E.pow_mem (hg 0) _) (E.pow_mem (hg 1) _))
      (E.pow_mem (hg 2) _)) (E.pow_mem (hg 3) _)
  have hl : 16 ≤ Nat.card E := by
    have hi : Function.Injective (fun i : Fin 16 => (⟨word i, hw i⟩ : E)) := by
      intro i j hij
      exact word_injective (congrArg Subtype.val hij)
    simpa using Nat.card_le_card_of_injective _ hi
  have he : E = pCore 2 first := eq_of_le_of_card_ge hle (by
    rw [← pairAction_ker_eq_twoCore, pairAction_ker_card]
    exact hl)
  exact he ▸ hE

/-- The fixed pair used by the source-cover calculation has elementary core. -/
theorem m22DisjointPair_twoCore_elementary :
    IsElementaryAbelian 2 (pCore 2 m22DisjointPairStabilizer) := by
  let := m22Pair_twoCore_elementary
  have h := IsElementaryAbelian.map (p := 2) (A := pCore 2 m22PairStabilizer)
    m22DisjointPairEquiv.toMonoidHom
  rwa [pCore_map_iso] at h

end Sporadic.Mathieu
