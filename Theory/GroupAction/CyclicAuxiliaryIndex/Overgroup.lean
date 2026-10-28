module

public import Theory.GroupAction.CyclicAuxiliaryIndex
public import Theory.GroupTheory.PCoreImage

/-!
# A centralizing auxiliary subgroup in an explicit overgroup

Let B and C be normal relative to a finite group J, with B ≤ J and C ≤ J.
Set N = C O₂(J). Relative normality gives O₂(B) ≤ N and mutual
normalization of B and N. If t normalizes J and centralizes C/O₂(C),
then it centralizes N/O₂(N): write an element of N as a product from
C and O₂(J), and bound the two commutators by the intrinsic core of N.

When t also normalizes B and B/O₂(B) is abelian, the cyclic auxiliary
index bound now has denominator N. The explicit supplement D satisfies
B join D = J; no identification with a separately marked subgroup is needed.

Source application: the full-product calculation in Aschbacher–Smith
13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupAction.CyclicAuxiliaryIndex
variable {G : Type*} [Group G]

/-- Normality here is relative to the explicit overgroup J. -/
theorem overgroup_normalizes_auxiliary (C J : Subgroup G)
    (hJC : J ≤ normalizer (C : Set G)) :
    J ≤ normalizer ((C ⊔ J.pCoreIn 2 : Subgroup G) : Set G) :=
  (le_inf hJC (J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The intrinsic core of a normal subgroup lies in the enlarged auxiliary. -/
theorem core_le_auxiliary (B C J : Subgroup G) (hBJ : B ≤ J)
    (hJB : J ≤ normalizer (B : Set G)) :
    B.pCoreIn 2 ≤ C ⊔ J.pCoreIn 2 :=
  (pCoreIn_mono_of_normalizes hBJ hJB).trans le_sup_right

/-- Enlarging C by O₂(J) retains centralization modulo the intrinsic two-core. -/
theorem auxiliary_commutator_core (C J : Subgroup G) (hCJ : C ≤ J)
    (hJC : J ≤ normalizer (C : Set G)) (t : G)
    (htJ : t ∈ normalizer (J : Set G))
    (hCt : ⁅C, zpowers t⁆ ≤ C.pCoreIn 2) :
    ⁅C ⊔ J.pCoreIn 2, zpowers t⁆ ≤ (C ⊔ J.pCoreIn 2).pCoreIn 2 := by
  let P := J.pCoreIn 2
  let N := C ⊔ P
  have hNJ : N ≤ J := sup_le hCJ (pCoreIn_le 2 J)
  have hJP : J ≤ normalizer (P : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hCN : C.pCoreIn 2 ≤ N.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (hNJ.trans hJC)
  have hPN : P ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) le_sup_right (hNJ.trans hJP)
  have hPt : ⁅P, zpowers t⁆ ≤ P := le_normalizer_iff_commutator_le_left.mp
    (zpowers_le.mpr (normalizer_le_normalizer_characteristic_image J (pCore 2 J) htJ))
  have hNcore : N ≤ normalizer (N.pCoreIn 2 : Set G) := N.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  apply commutator_le.mpr
  intro x hx s hs
  have hx' : x ∈ (C : Set G) * (P : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right C P (hCJ.trans hJP)]
    exact hx
  obtain ⟨c, hc, p, hp, rfl⟩ := hx'
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact (N.pCoreIn 2).mul_mem
    (le_normalizer_iff.mp hNcore c (mem_sup_left hc) _
      (hPN (hPt (commutator_mem_commutator hp hs))))
    (hCN (hCt (commutator_mem_commutator hc hs)))

variable [Finite G]

/-- The full carrier is B join D; D need not be the marked cubic subgroup. -/
theorem commutator_twoCore_card_le_overgroup (B C J D : Subgroup G)
    (hJD : B ⊔ D = J) (hCJ : C ≤ J)
    (hJB : J ≤ normalizer (B : Set G)) (hJC : J ≤ normalizer (C : Set G))
    (habelian : ⁅B, B⁆ ≤ B.pCoreIn 2) (t : G)
    (htB : t ∈ normalizer (B : Set G)) (htJ : t ∈ normalizer (J : Set G))
    (hCt : ⁅C, zpowers t⁆ ≤ C.pCoreIn 2) :
    let A : Subgroup G := ⁅B, zpowers t⁆
    Nat.card (A ⧸ pCore 2 A) ≤ (C ⊔ J.pCoreIn 2).relIndex J := by
  have hBJ : B ≤ J := hJD ▸ le_sup_left
  have hNJ : C ⊔ J.pCoreIn 2 ≤ J := sup_le hCJ (pCoreIn_le 2 J)
  have h := commutator_twoCore_card_le B (C ⊔ J.pCoreIn 2) D
    (hBJ.trans (overgroup_normalizes_auxiliary C J hJC)) (hNJ.trans hJB)
    habelian t htB (auxiliary_commutator_core C J hCJ hJC t htJ hCt)
  rwa [sup_eq_left.mpr (core_le_auxiliary B C J hBJ hJB), hJD] at h

end Theory.GroupAction.CyclicAuxiliaryIndex
