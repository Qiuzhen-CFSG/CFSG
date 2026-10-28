module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual


/-!
# The HS pair kernel lies in the two-residual

For each of the five checked generators `q k` of the actual kernel of order
64, an explicit local word `u` has odd order and so does `(q k) * u`. Thus
`q k = ((q k) * u) * u⁻¹` belongs to the two-residual. The previously constructed
quaternion and cyclic factors then put the entire kernel in that residual.

The five-cycle lift comes from the word used in `PairQuotient`; taking its
fourth power gives order five. All word identities and odd-power relations
are checked by Lean's kernel on the actual degree-100 permutations. The
untrusted discovery script is retained in `source/discover.py`; it supplies
no proof input. ATLAS attribution is inherited from the existing carrier.

Source: Aschbacher–Smith, 16.1.5(10), printed p.1172, and the comparison in
16.4.11(2), printed p.1193. This proves a model fact beyond the extension
shape alone; no splitting or kernel-action hypothesis is imposed.
-/

open Subgroup
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open HSInner HSInner.CoreStructure
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HSCoreNormalOrders
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

private def letterA : Carrier := ⟨ab0, by
  rw [ab0_eq]
  exact Subgroup.subset_closure (by simp)⟩
private def letterB : Carrier := ⟨ab1, by
  rw [ab1_eq]
  exact Subgroup.subset_closure (by simp)⟩
private def seed : Carrier := letterB ^ 2 * letterA * letterB
private def cycle : Carrier := (seed * (e0 * seed⁻¹ * e0 * seed) ^ 2) ^ 4
private def oddHelper (k : Fin 5) : Carrier :=
  ![cycle, s1 * cycle * s1, cycle * s1 * cycle * s1 * q 3,
    cycle, cycle * cycle * s1 * q 2 * cycle * s1] k
private def oddExponent (k : Fin 5) : ℕ := ![5, 5, 3, 5, 3] k

private theorem helper_commutes (k : Fin 5) : oddHelper k * e0 = e0 * oddHelper k := by
  have h : ∀ k : Fin 5, ∀ i : Fin 100,
      ((oddHelper k * e0).val i) = ((e0 * oddHelper k).val i) := by
    apply allFin
    decide +kernel
  apply Subtype.ext
  exact Equiv.ext (h k)

private def helperLocal (k : Fin 5) : localGroup 0 :=
  ⟨oddHelper k, by
    rw [localGroup_zero_eq_centralizer]
    exact mem_centralizer_singleton_iff.mpr (helper_commutes k)⟩

private theorem odd_powers : ∀ k : Fin 5,
    helperLocal k ^ oddExponent k = 1 ∧
    ((qElement k).val * helperLocal k) ^ oddExponent k = 1 := by
  decide +kernel

private theorem odd_coprime (k : Fin 5) : Nat.Coprime 2 (oddExponent k) := by
  fin_cases k <;> decide

private theorem q_mem_residual (k : Fin 5) : (qElement k).val ∈ pResidual 2 (localGroup 0) := by
  have h₁ := mem_pResidual_of_orderOf_coprime
    ((odd_coprime k).of_dvd_right (orderOf_dvd_of_pow_eq_one (odd_powers k).1))
  have h₂ := mem_pResidual_of_orderOf_coprime
    ((odd_coprime k).of_dvd_right (orderOf_dvd_of_pow_eq_one (odd_powers k).2))
  simpa using (pResidual 2 (localGroup 0)).mul_mem h₂
    ((pResidual 2 (localGroup 0)).inv_mem h₁)

/-- The actual normal pair kernel is contained in the local two-residual. -/
public theorem core_le_residual : core ≤ pResidual 2 (localGroup 0) := by
  let H := (pResidual 2 (localGroup 0)).comap core.subtype
  have hq (k : Fin 5) : qElement k ∈ H := q_mem_residual k
  have hli : leftI ∈ H := H.mul_mem (hq 0) (hq 2)
  have hlj : leftJ ∈ H := H.mul_mem (hq 1) (hq 3)
  have hri : rightI ∈ H := H.mul_mem (hq 0) (hq 3)
  have hrj : rightJ ∈ H := H.mul_mem (H.mul_mem (hq 0) (hq 1)) (hq 2)
  have hcy : cyclicGenerator ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hq 0) (hq 1)) (hq 2)) (hq 3)) (hq 4)
  have hleft : leftFactor ≤ H := by
    rintro x ⟨u, rfl⟩
    cases u with
    | a n => exact H.pow_mem hli _
    | xa n => exact H.mul_mem hlj (H.pow_mem hli _)
  have hright : rightFactor ≤ H := by
    rintro x ⟨u, rfl⟩
    cases u with
    | a n => exact H.pow_mem hri _
    | xa n => exact H.mul_mem hrj (H.pow_mem hri _)
  have hcyclic : cyclicPart ≤ H := by
    rintro x ⟨u, rfl⟩
    exact H.pow_mem hcy _
  have he : embeddedCore = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup core) ≃* core).toEquiv,
      embeddedCore_card] using core_card_le
  have hH : (⊤ : Subgroup core) ≤ H := by
    rw [← he]
    exact sup_le (sup_le hleft hright) hcyclic
  intro x hx
  exact hH (show (⟨x, hx⟩ : core) ∈ ⊤ from trivial)
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HSCoreNormalOrders
