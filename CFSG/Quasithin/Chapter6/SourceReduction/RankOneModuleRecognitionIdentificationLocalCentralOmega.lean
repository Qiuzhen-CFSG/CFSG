module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNormalizers
public import Theory.GroupTheory.SylowCentralizerComplement

/-!
# Central omega in the natural layer

An element of Ω₁(Z(T)) lying in R is fixed by the Sylow of L modulo
[R,L]. Averaging over the odd Sylow index gives an L-fixed representative
in its [R,L]-coset. That representative belongs to T, so C_T(L) = 1
forces the original element into [R,L], and hence into Z_S.

The Chapter 12 companion proves the required containment in the actual
reduced subgroup R₂(LT). This is the containment at the start of §6.2,
not yet the order-two conclusion of 6.2.2.
Source: Aschbacher--Smith, §6.2, printed p.680.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
/-- The natural layer absorbs the central omega subgroup once it lies in R. -/
theorem local_centralOmega_le_ZS_of_le_reduced
    (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hZR : centralOmega (T : Subgroup G) ≤ R) :
    centralOmega (T : Subgroup G) ≤ ZS (T : Subgroup G) L R := by
  let := h.layer_elementary
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes_L
  have hZ : centralOmega (T : Subgroup G) ≤
      (T : Subgroup G) ⊓ centralizer (T : Set G) := omegaOneAmbient_le _
  intro z hz
  have hzT := hZ hz
  have hzB : z ∈ layer L R := by
    obtain ⟨v, hv, hvc⟩ := fixed_coset_of_sylow L (layer L R)
      (normalizer_commutator_ge_right R L)
      (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) S z
      (fun l hl => by
        change ⁅l, z⁆ ∈ ⁅R, L⁆
        rw [commutator_comm]
        exact commutator_mem_commutator hl (hZR hz))
      (fun l hl => by
        have hlT : (l : G) ∈ (T : Subgroup G) := by
          have hh : l ∈ (T : Subgroup G).subgroupOf L := hS ▸ hl
          exact hh
        exact hzT.2 l hlT)
    have hvcT : v * z ∈ (T : Subgroup G) := (T : Subgroup G).mul_mem (h.layer_le_T hv) hzT.1
    have he : v * z = 1 := show v * z ∈ (⊥ : Subgroup G) from
      hnatural.2.2.1 ▸ ⟨hvcT, hvc⟩
    have hzv : z = v⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [hzv]
    exact (layer L R).inv_mem hv
  exact ⟨hzB, centralizer_le inf_le_left hzT.2⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

