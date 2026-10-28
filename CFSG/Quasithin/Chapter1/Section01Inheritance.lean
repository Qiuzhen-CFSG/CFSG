module

public import Theory.GroupTheory.CharacteristicTwoInheritance
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# Characteristic-two inheritance in Chapter 1

These are Aschbacher–Smith 1.1.3(1–3) and 1.1.4(4), printed pp.500–501
(PDF pp.517–518), combined manuscript of 1 March 2004. Part 1.1.3(1)
is re-exported from the checked Sylow extension. All relative cores,
centralizers and normalizers are taken in the indicated overgroup.

The general prime-core criterion excludes prime-order elements of order
prime to p by the proved P × Q centralizer theorem. It yields the sandwich
clause; normality inside the normalizer gives the centralizer clause.
Successive normalizers give the ordered finite-intersection clause.
-/

public section
namespace CFSG.Quasithin.Chapter1
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- 1.1.3(2), including both the sandwich subgroup and the relative centralizer. -/
theorem lemma_1_1_3_2 {M X H : Subgroup G} (hM : M ∈ He G)
    (hXp : IsPGroup 2 X) (hXM : X ≤ M)
    (hXCH : X ⊔ (M ⊓ centralizer (X : Set G)) ≤ H)
    (hHN : H ≤ M ⊓ normalizer (X : Set G)) :
    H ∈ He G ∧ M ⊓ centralizer (X : Set G) ∈ He G :=
  ⟨pCoreIn_selfCentralizing_of_normalizer_sandwich hM hXp
      (le_sup_left.trans hXCH) (le_sup_right.trans hXCH)
      (hHN.trans inf_le_left) (hHN.trans inf_le_right),
    pCoreIn_selfCentralizing_centralizer hM hXp hXM⟩

/-- The normalizer specialization of 1.1.3(2). -/
theorem normalizer_mem_He_of_isPGroup {M X : Subgroup G} (hM : M ∈ He G)
    (hXp : IsPGroup 2 X) (hXM : X ≤ M) :
    M ⊓ normalizer (X : Set G) ∈ He G :=
  pCoreIn_selfCentralizing_normalizer hM hXp hXM

/-- 1.1.3(3). `M ⊓ iInf ...` is the intersection taken inside M,
including the empty-family convention. The source's ordered relative
normalization hypothesis `Bⱼ ≤ N_H(Bᵢ)` for `i ≤ j` is retained literally. -/
theorem lemma_1_1_3_3 {M H : Subgroup G} (hM : M ∈ He G) (hHM : H ≤ M)
    {n : ℕ} (B : Fin n → Subgroup G) (hp : ∀ i, IsPGroup 2 (B i))
    (hBH : ∀ i, B i ≤ H)
    (hnorm : ∀ i j, i ≤ j → B j ≤ H ⊓ normalizer (B i : Set G))
    (hH : H = M ⊓ ⨅ i, normalizer (B i : Set G)) : H ∈ He G := by
  change H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2
  have hc := pCoreIn_selfCentralizing_iInf_normalizer hM B hp
    (fun i => (hBH i).trans hHM) (fun i j hij => (hnorm i j hij).trans inf_le_right)
  simpa only [← hH] using hc

/-- 1.1.4(4): no normality of N in M is required. -/
theorem lemma_1_1_4_4 {M N : Subgroup G} (_hN : N ≠ ⊥)
    (hNM : N ≤ M) (hM : M ∈ He G)
    (hR : M.pCoreIn 2 ⊓ centralizer (N.pCoreIn 2 : Set G) ≤ N) :
    N ∈ He G :=
  pCoreIn_selfCentralizing_of_core_centralizer_le hM hNM hR

/-- Intrinsic form of 1.1.3(2), as consumed by the central-involution
selection argument of 16.2.1. -/
theorem characteristicTwo_normalizer (H : Subgroup G) (X : Subgroup H)
    (hX : IsPGroup 2 X) (hH : HasCharacteristicTwo H) :
    HasCharacteristicTwo (normalizer (X : Set H)) :=
  normalizer_core_selfCentralizing hH X hX

end CFSG.Quasithin.Chapter1
