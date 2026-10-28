module

public import Theory.Mathieu.M22.Properties.PairHexadIncidence
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients
public import Theory.GroupTheory.SylowKernelCore

/-!
# The pair two-core inside each incident hexad stabilizer

The five-hexad permutation action has the pair two-core as its kernel.
Consequently that core stabilizes every incident hexad. Simultaneous flag
conjugacy transports this statement with its literal subgroup embeddings.
For the pair {0,4}, the hexad named `m22Hexad234` is incident (22 is 0 in
Fin 22). Its pair core has order sixteen and quotient S₅.

Source: Aschbacher–Smith I.2.2(6a), printed p.412. This locates the second
elementary restriction for the cover calculation; it does not identify the
pair kernel with the pointwise hexad kernel.
-/

public section
namespace Sporadic.Mathieu
open Subgroup MulAction M22ValueBound.Concrete
open scoped Pointwise

/-- The standard pair core fixes every hexad in its five-hexad pencil. -/
theorem m22Pair_twoCore_le_hexad {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) (hPB : m22Pair12 ⊆ B) :
    m22PairStabilizer.pCoreIn 2 ≤ stabilizer M22 B := by
  have hb : B ∈ m22Blocks.filter (m22Pair12 ⊆ ·) := Finset.mem_filter.mpr ⟨hB, hPB⟩
  rw [pairHexads_complete] at hb
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
  rintro _ ⟨g, hg, rfl⟩
  have hk : pairAction g = 1 := by
    change g ∈ pairAction.ker
    rw [pairAction_ker_eq_twoCore]
    exact hg
  change g.val • pairHexad i = pairHexad i
  simpa only [hk, Equiv.Perm.one_apply, Finset.smul_finset_def, Subgroup.smul_def]
    using (pairAction_spec g i).symm

/-- Both the pair and the hexad retain the same native conjugator. -/
theorem m22_pair_twoCore_le_incident_hexad {S B : Finset (Fin 22)}
    (hS : S.card = 2) (hB : B ∈ m22Blocks) (hSB : S ⊆ B) :
    (stabilizer M22 S).pCoreIn 2 ≤ stabilizer M22 B := by
  obtain ⟨g, hgS, hgB⟩ := m22_pair_hexad_flag_conjugacy hS hB hSB
  have h := map_mono (f := (MulAut.conj g).toMonoidHom)
    (m22Pair_twoCore_le_hexad m22Hexad123_mem (by decide +kernel))
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective] at h
  change ((stabilizer M22 m22Pair12).map (MulAut.conj g).toMonoidHom).pCoreIn 2 ≤
    (stabilizer M22 m22Hexad123).map (MulAut.conj g).toMonoidHom at h
  rwa [← stabilizer_smul_eq_stabilizer_map_conj, ← stabilizer_smul_eq_stabilizer_map_conj,
    hgS, hgB] at h

theorem m22DisjointPair04_subset_hexad234 : m22DisjointPair04 ⊆ m22Hexad234 := by
  decide +kernel

/-- An actual conjugation equivalence, obtained from an incident flag. -/
noncomputable def m22DisjointPairEquiv : m22PairStabilizer ≃* m22DisjointPairStabilizer := by
  let h := m22_pair_hexad_flag_conjugacy m22DisjointPair04_card m22Hexad234_mem
    m22DisjointPair04_subset_hexad234
  exact stabilizerEquivStabilizer h.choose_spec.1.symm

theorem m22DisjointPairStabilizer_card : Nat.card m22DisjointPairStabilizer = 1920 :=
  (Nat.card_congr m22DisjointPairEquiv.toEquiv).symm.trans m22PairStabilizer_card

theorem m22DisjointPair_twoCore_card : Nat.card (pCore 2 m22DisjointPairStabilizer) = 16 := by
  rw [← pCore_map_iso 2 m22DisjointPairEquiv,
    card_map_of_injective m22DisjointPairEquiv.injective,
    ← pairAction_ker_eq_twoCore]
  exact pairAction_ker_card

/-- The quotient identification keeps the actual pair two-core as denominator. -/
noncomputable def m22DisjointPairQuotientEquiv :
    (m22DisjointPairStabilizer ⧸ pCore 2 m22DisjointPairStabilizer) ≃*
      Equiv.Perm (Fin 5) :=
  (QuotientGroup.congr _ _ m22DisjointPairEquiv
    (pCore_map_iso 2 m22DisjointPairEquiv)).symm.trans firstQuotientEquiv

theorem m22DisjointPair_twoCore_le_hexad234 :
    m22DisjointPairStabilizer.pCoreIn 2 ≤ stabilizer M22 m22Hexad234 :=
  m22_pair_twoCore_le_incident_hexad m22DisjointPair04_card m22Hexad234_mem
    m22DisjointPair04_subset_hexad234

end Sporadic.Mathieu
