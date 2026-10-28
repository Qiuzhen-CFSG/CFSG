module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Thompson
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingNormalizerAction

/-!
# The original alternating marking on the reduced group

The actual normalizer action extends the original marked action on K Baum(R).
Whenever T normalizes K and contains that original Baumann subgroup, its
restriction to KT is onto S₅: it contains both the original A₅ image and a
marked transposition. Its kernel is the literal module centralizer.

Source: Aschbacher–Smith, C.5.4 and C.5.9, printed pp.155 and161.
-/
public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource ChapterB.Offenders
variable {G : Type*} [Group G] {R K L : Subgroup G}

private theorem alternating_action_surjective (h : AlternatingPairSetup R K L) :
    Function.Surjective h.action := by
  have hA : alternatingGroup (Fin 5) ≤ h.action.range :=
    h.block_image.symm ▸ map_le_range _ _
  have hdvd := index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hi | hi
  · exact MonoidHom.range_eq_top.mp (index_eq_one.mp hi)
  · have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    have ht : pairSwap 5 0 ∈ h.action.range :=
      (map_le_range _ _) (h.baumann_image.symm ▸
        (show pairSwap 5 0 ∈ ChapterB.Offenders.D 5 from
          ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide)))
    rw [he] at ht
    have hnot : pairSwap 5 0 ∉ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    exact (hnot ht).elim

/-- The reduced KT action uses the same original coordinates and agrees with
its full original K Baum(R) marking. -/
theorem alternating_reduced_action (h : AlternatingPairSetup R K L)
    (T : Subgroup G) (hn : T ≤ normalizer (K : Set G))
    (hST : ChapterB.baumann R ≤ T) :
    ∃ q : (K ⊔ T : Subgroup G) →* FivePerm,
      Function.Surjective q ∧
      q.ker = (centralizer (sourceModule K : Set G)).subgroupOf (K ⊔ T) ∧
      ∀ s : (K ⊔ ChapterB.baumann R : Subgroup G),
        q (inclusion (sup_le_sup_left hST K) s) = h.action s := by
  obtain ⟨a,hker,ha⟩ := h.exists_normalizer_action
  let q := a.comp (inclusion (sup_le K.le_normalizer hn))
  have hcompat (s : (K ⊔ ChapterB.baumann R : Subgroup G)) :
      q (inclusion (sup_le_sup_left hST K) s) = h.action s := ha s
  refine ⟨q,?_,?_,hcompat⟩
  · intro p
    obtain ⟨s,rfl⟩ := alternating_action_surjective h p
    exact ⟨inclusion (sup_le_sup_left hST K) s,hcompat s⟩
  · ext s
    change inclusion (sup_le K.le_normalizer hn) s ∈ a.ker ↔ _
    rw [hker]
    rfl
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
