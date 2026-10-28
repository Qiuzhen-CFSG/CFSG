module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootGeometry
import Mathlib.GroupTheory.Coset.Card

/-!
# The even centralizer of two disjoint transpositions in S7

The first C2 factor exchanges both marked pairs. An S3 permutation acts on
letters 2, 3 and 6, with its sign compensated by the transposition (45).
This gives an explicit faithful homomorphism into the even centralizer of
(01) and (45). A kernel-checked count of that concrete subgroup proves
surjectivity, giving C2 x S3 as an actual group equivalence.

This is the finite calculation used after the full ambient reduction in
Held 5.11 (1969), DOI 10.1215/ijm/1256053756, p.239. It does not by itself
identify any ambient centralizer in the arbitrary group G.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

private def restIndex : Fin 3 → Fin 7 := ![2, 3, 6]
private def restPerm (p : Perm (Fin 3)) : Perm (Fin 7) where
  toFun := ![0, 1, restIndex (p 0), restIndex (p 1), 4, 5, restIndex (p 2)]
  invFun := ![0, 1, restIndex (p⁻¹ 0), restIndex (p⁻¹ 1), 4, 5, restIndex (p⁻¹ 2)]
  left_inv := by revert p; decide +kernel
  right_inv := by revert p; decide +kernel

private def pairFun (x : CrossingModel) : Perm (Fin 7) :=
  (if x.1 = 1 then 1 else swap 0 1 * swap 4 5) *
  (if Perm.sign x.2 = 1 then 1 else swap 4 5) * restPerm x.2

private def pairHom : CrossingModel →* Perm (Fin 7) where
  toFun := pairFun
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem pairHom_injective : Function.Injective pairHom := by decide +kernel

private theorem pairHom_mem (x : CrossingModel) : pairHom x ∈ evenPairCentralizer := by
  change Perm.sign (pairHom x) = 1 ∧
    ∀ p ∈ ({swap 0 1, swap 4 5} : Set (Perm (Fin 7))), p * pairHom x = pairHom x * p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  revert x
  decide +kernel

private theorem pair_count :
    (Finset.univ.filter fun p : Perm (Fin 7) =>
      swap 0 1 * p = p * swap 0 1 ∧ swap 4 5 * p = p * swap 4 5 ∧
        Perm.sign p = 1).card = 12 := by
  decide +kernel

/-- The exact even centralizer of the two marked disjoint transpositions. -/
public noncomputable def evenPairEquiv : evenPairCentralizer ≃* CrossingModel := by
  classical
  let f : CrossingModel →* evenPairCentralizer := pairHom.codRestrict _ pairHom_mem
  have hf : Function.Injective f := fun a b h =>
    pairHom_injective (congrArg Subtype.val h)
  have hcard : Fintype.card evenPairCentralizer = 12 := by
    rw [Fintype.card_subtype]
    simpa only [evenPairCentralizer, mem_inf, Perm.mem_alternatingGroup,
      mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, and_comm, and_left_comm, and_assoc] using pair_count
  have hc : Fintype.card CrossingModel = 12 := by decide +kernel
  exact (MulEquiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hc.trans hcard.symm⟩)).symm

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
