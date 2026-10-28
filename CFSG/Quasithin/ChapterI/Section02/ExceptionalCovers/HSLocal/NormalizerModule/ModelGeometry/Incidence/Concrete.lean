module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.ModelGeometry.Core
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelCore

/-!
# Concrete HS centralizer incidences and a marked involution

The C₄³ normalizer core lies in the alternating preimage of the fixed-pair
quotient. For each of its three generators, an explicit local square times
the generator fixes every pair, proving this inclusion without identifying
the alternating preimage with the two-residual. The cyclic central factor
has coordinates (1,2,0). The elementary eight lies in the pair kernel, which
also contains the normalizing involution s0 outside the C₄³ core. Its fixed
letter 1 certifies the two-central marking.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423;
GLS3 Table 5.3m. The script in `source/` is untrusted discovery only. All
permutation identities below are bounded, kernel-checked certificates.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open Theory.GroupTheory.DoubleCoverCentralizer
set_option maxRecDepth 20000

@[expose] def P : Subgroup Carrier := core.map (localGroup 0).subtype
@[expose] noncomputable def T : Subgroup Carrier :=
  CentralizerRestriction.modelResidual.map (localGroup 0).subtype
@[expose] def W : Subgroup Carrier := (cyclicPart.map core.subtype).map (localGroup 0).subtype

private theorem root_mem_A (i : Fin 3) : CoreGeometry.root i ∈ A := by
  let x : Multiplicative (Fin 3 → ZMod 4) := .ofAdd (fun j => if j = i then 1 else 0)
  have h : ((CoreGeometry.coreCoordinates x).val : Carrier) = CoreGeometry.root i := by
    rw [CoreGeometry.coreCoordinates_apply]
    fin_cases i <;> simp [x] <;> exact pow_one _
  rw [← h]
  exact mem_map_of_mem _ (CoreGeometry.coreCoordinates x).property

private theorem root_mem_local (i : Fin 3) : CoreGeometry.root i ∈ localGroup 0 := by
  rw [localGroup_zero_eq_centralizer]
  exact A_le_marked_centralizer (root_mem_A i)

private theorem P_le_T : P ≤ T := by
  apply map_mono
  intro x hx
  change CentralNormalizerThreePart.PairQuotient.fiveHom x ∈ alternatingGroup (Fin 5)
  have h : CentralNormalizerThreePart.PairQuotient.fiveHom x = 1 := by
    rwa [← MonoidHom.mem_ker, CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
  rw [h]
  exact one_mem _

private theorem square_mem_T (x : Carrier) (hx : x ∈ localGroup 0) : x ^ 2 ∈ T := by
  refine mem_map_of_mem (localGroup 0).subtype (x := (⟨x, hx⟩ : localGroup 0) ^ 2) ?_
  change CentralNormalizerThreePart.PairQuotient.fiveHom ((⟨x, hx⟩ : localGroup 0) ^ 2) ∈
    alternatingGroup (Fin 5)
  rw [Equiv.Perm.mem_alternatingGroup, map_pow, map_pow, Int.units_sq]

private theorem sylow_mem_local (i : Fin 3) : sylowGenerator i ∈ localGroup 0 := by
  rw [localGroup_zero_eq_centralizer, mem_centralizer_singleton_iff]
  have h : ∀ (i : Fin 3) (p : Fin 100),
      ((sylowGenerator i * e0 : Carrier) : Equiv.Perm (Fin 100)) p =
      ((e0 * sylowGenerator i : Carrier) : Equiv.Perm (Fin 100)) p := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

private def letterA : Carrier := ⟨ab0, by rw [ab0_eq]; exact generatorAElement.property⟩
private def letterB : Carrier := ⟨ab1, by rw [ab1_eq]; exact generatorBElement.property⟩
private def seed : Carrier := letterB ^ 2 * letterA * letterB
private def cycle : Carrier := seed * (e0 * seed⁻¹ * e0 * seed) ^ 2
private theorem cycle_mem_local : cycle ∈ localGroup 0 := by
  rw [localGroup_zero_eq_centralizer, mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Equiv.ext
  apply SylowCatalogueData.allFin
  decide +kernel

private def squareWitness (i : Fin 3) : Carrier := ![1, s2 * s1, cycle ^ 2 * s1 * cycle] i
private theorem squareWitness_mem_local (i : Fin 3) : squareWitness i ∈ localGroup 0 := by
  have h1 := sylow_mem_local 1
  have h2 := sylow_mem_local 2
  fin_cases i
  · exact one_mem _
  · exact mul_mem h2 h1
  · exact mul_mem (mul_mem (pow_mem cycle_mem_local 2) h1) cycle_mem_local

private def correctionLocal (i : Fin 3) : localGroup 0 :=
  ⟨squareWitness i ^ 2 * CoreGeometry.root i,
    mul_mem (pow_mem (squareWitness_mem_local i) 2) (root_mem_local i)⟩

private theorem correction_mem_core (i : Fin 3) : correctionLocal i ∈ core := by
  apply (mem_core_iff _).mpr
  have h : ∀ (i : Fin 3) (p : Fin 100), (e0 : Equiv.Perm (Fin 100)) p = p →
      (correctionLocal i).val.val p = p ∨ (correctionLocal i).val.val p = twin p := by
    apply allFin₂
    decide +kernel
  exact h i

private theorem root_mem_T (i : Fin 3) : CoreGeometry.root i ∈ T := by
  have hc : squareWitness i ^ 2 * CoreGeometry.root i ∈ T :=
    P_le_T (mem_map_of_mem (localGroup 0).subtype (correction_mem_core i))
  exact (mul_mem_cancel_left (square_mem_T _ (squareWitness_mem_local i))).mp hc

/-- The actual normalizer core is contained in the alternating preimage. -/
theorem A_le_T : A ≤ T := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨v, hv⟩ := CoreGeometry.coreCoordinates_bijective.surjective ⟨x, hx⟩
  have he := congrArg (fun q : pCore 2 baseNormalizer => (q.val : Carrier)) hv
  rw [CoreGeometry.coreCoordinates_apply] at he
  change (x : Carrier) ∈ T
  change _ = (x : Carrier) at he
  rw [← he]
  exact mul_mem (mul_mem (pow_mem (root_mem_T 0) _) (pow_mem (root_mem_T 1) _))
    (pow_mem (root_mem_T 2) _)

private theorem elementary_mem_core (i : Fin 3) :
    (⟨elementaryGenerator i, by
      rw [localGroup_zero_eq_centralizer]
      exact A_le_marked_centralizer (elementary_le_A
        (subset_closure ⟨i, Fin.le_last i, rfl⟩))⟩ : localGroup 0) ∈ core := by
  apply (mem_core_iff _).mpr
  have h : ∀ (i : Fin 3) (p : Fin 100), (e0 : Equiv.Perm (Fin 100)) p = p →
      (elementaryGenerator i : Equiv.Perm (Fin 100)) p = p ∨
        (elementaryGenerator i : Equiv.Perm (Fin 100)) p = twin p := by
    apply allFin₂
    decide +kernel
  exact h i

/-- The elementary eight lies in the literal centralizer pair kernel. -/
theorem elementary_le_P : baseElementary ≤ P := by
  apply (closure_le _).mpr
  rintro _ ⟨i, _, rfl⟩
  exact mem_map_of_mem (localGroup 0).subtype (elementary_mem_core i)

/-- Coordinates of the distinguished cyclic fourth root in the normalizer core. -/
theorem cyclicGenerator_coordinates : cyclicGenerator.val.val =
    ((CoreGeometry.coreCoordinates (.ofAdd ![1, 2, 0])).val : Carrier) := by
  rw [CoreGeometry.coreCoordinates_apply]
  apply Subtype.ext
  apply Equiv.ext
  apply SylowCatalogueData.allFin
  decide +kernel

private theorem cyclicGenerator_mem_A : cyclicGenerator.val.val ∈ A := by
  rw [cyclicGenerator_coordinates]
  exact ⟨(CoreGeometry.coreCoordinates (.ofAdd ![1, 2, 0])).val,
    (CoreGeometry.coreCoordinates (.ofAdd ![1, 2, 0])).property, rfl⟩

/-- The marked cyclic factor is inside the actual normalizer core. -/
theorem W_le_A : W ≤ A := by
  rintro _ ⟨x, ⟨y, ⟨n, rfl⟩, rfl⟩, rfl⟩
  exact A.pow_mem cyclicGenerator_mem_A n.toAdd.val

theorem W_le_normalizer : W ≤ baseNormalizer := W_le_A.trans A_le_normalizer

/-- The source's marked normalizer involution. -/
@[expose] def j₀ : Carrier := s0

theorem j₀_mem_normalizer : j₀ ∈ baseNormalizer :=
  baseSylow_le_normalizer (subset_closure ⟨0, rfl⟩)

private theorem q_zero_eq_j₀ : (qElement 0).val.val = j₀ := by
  apply Subtype.ext
  apply Equiv.ext
  apply SylowCatalogueData.allFin
  decide +kernel

theorem j₀_mem_P : j₀ ∈ P := by
  rw [← q_zero_eq_j₀]
  exact mem_map_of_mem _ (qElement 0).property

theorem j₀_order : orderOf j₀ = 2 := by
  apply (orderOf_eq_prime_iff (p := 2)).mpr
  constructor
  · apply Subtype.ext
    apply Equiv.ext
    apply SylowCatalogueData.allFin
    decide +kernel
  · intro he
    have h := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 4) he
    revert h
    decide +kernel

theorem j₀_not_mem_A : j₀ ∉ A := by
  intro h
  have hc := A_le_elementary_centralizer h
  have he : e1 ∈ baseElementary := subset_closure ⟨1, Fin.le_last 1, rfl⟩
  have hh := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 1) (hc e1 he)
  revert hh
  decide +kernel

/-- The marking is certified by an actual fixed permutation letter. -/
theorem j₀_twoCentral : TwoCentral j₀ :=
  twoCentral_of_fixed_letter j₀ j₀_order 1 (by decide +kernel)


end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
