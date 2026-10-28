module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Quotient
public import Theory.GroupTheory.PCoreQuotientBorelNormalizer
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki

/-!
# Normalizer lifts for a T-invariant Suzuki component

The Suzuki quotient is centerless and has odd outer automorphism group.
Consequently the original Sylow subgroup acts on it by inner automorphisms.
The two-core supplement calculation puts N_I(T ∩ I) in N_G(T). Combined
with the surjective Borel coefficient map, this supplies every normalizer
lift in the fixed-component branch. T need not be contained in I.

The orbit of two components still requires its diagonal normalizer
calculation. Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

public noncomputable section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G} {m : ℕ}

private theorem center_outer {Q : Type*} [Group Q]
    (hm : 0 < m) (e : Q ≃* SuzukiMatrixGroup m) :
    center Q = ⊥ ∧ Nat.Coprime 2 (Nat.card (MulAut.Outer Q)) := by
  have hmodel : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
  let := hmodel.isSimple
  have hz : center (SuzukiMatrixGroup m) = ⊥ := by
    rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hmodel.not_commutative (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := h.symm ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm)).elim
  constructor
  · apply eq_bot_iff.mpr
    intro q hq
    have he : e q ∈ center (SuzukiMatrixGroup m) := (centerCongr e ⟨q, hq⟩).property
    rw [hz, mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  · rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact (suzuki_odd_outer_index m hm).coprime_two_left

/-- For a fixed component the whole orbit Borel normalizes the original T. -/
theorem borel_le_normalizer_of_fixed (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (hm : 0 < m) (e : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m) :
    borel T I ≤ normalizer (T : Set G) := by
  have he : orbit T I = I := le_antisymm (conjugateSpanBy_le le_rfl hTI)
    (le_conjugateSpanBy I (T : Subgroup G))
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  obtain ⟨hz, ho⟩ := center_outer hm e
  have hn := sylow_normalizer_le_of_coprime_outer T I hTI hz ho P hP
  change (normalizer ((P : Subgroup I) : Set I)).map I.subtype ≤ _ at hn
  rw [hP] at hn
  have hB : (borel T I).subgroupOf I =
      normalizer ((T : Subgroup G).subgroupOf I : Set I) := by
    rw [borel, he, inf_subgroupOf_left, subgroupOf_normalizer_eq inf_le_right,
      inf_subgroupOf_right]
  intro b hb
  have hbI : b ∈ I := he ▸ hb.1
  apply hn
  refine ⟨⟨b, hbI⟩, ?_, rfl⟩
  rw [← hB]
  exact hb

/-- Normalizer lifts are completely discharged in the fixed-component branch. -/
theorem OrbitCoordinates.normalizerLifts_of_fixed (c : OrbitCoordinates T I m)
    (hm : 0 < m) (hTI : (T : Subgroup G) ≤ normalizer (I : Set G)) :
    c.NormalizerLifts hm := by
  intro u
  obtain ⟨b, hb⟩ := c.coefficient_surjective hm u
  exact ⟨b, borel_le_normalizer_of_fixed hTI hm c.component b.property, hb⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
