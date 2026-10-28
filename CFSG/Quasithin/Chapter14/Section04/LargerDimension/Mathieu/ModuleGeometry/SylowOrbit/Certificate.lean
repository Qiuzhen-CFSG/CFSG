module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit.PairEdges
/-!
# Native Mathieu Sylow certificates

The parent tree reaches 129 distinct pairs. Hence the generated two-group has order at least 256. The native ambient Sylow order is 256, which makes this candidate an actual Sylow subgroup.

These are the finite certificates for H.12.1(9) and 14.4.12, printed
pp.393–394 and 1011–1012. See `source/README.md` for data provenance.
-/

@[expose] public section
noncomputable section
open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender Subgroup
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
namespace SylowCertificates
open OrbitCertificates


theorem pairs_reached (i : Fin 129) : ∃ g ∈ candidate,
    representation g (packed 1) = (pairVectors i).1 ∧
    representation g (packed 2) = (pairVectors i).2 := by
  have hall : ∀ n : ℕ, ∀ hn : n < 129, ∃ g ∈ candidate,
      representation g (packed 1) = (pairVectors ⟨n, hn⟩).1 ∧
      representation g (packed 2) = (pairVectors ⟨n, hn⟩).2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero =>
        refine ⟨1, candidate.one_mem, ?_⟩
        simp only [map_one, Module.End.one_apply]
        exact (show packed 1 = (pairVectors 0).1 ∧ packed 2 = (pairVectors 0).2 by
          decide +kernel)
      | succ n =>
        let k : Fin 128 := ⟨n, by omega⟩
        obtain ⟨g, hg, hv, hw⟩ := ih (pairParent k).val (pairParent_lt k) (pairParent k).isLt
        refine ⟨generator (pairActor k) * g,
          candidate.mul_mem (subset_closure ⟨_, rfl⟩) hg, ?_, ?_⟩
        · rw [map_mul, Module.End.mul_apply, hv]
          change (((generator (pairActor k) : Matrix12ˣ) : Matrix12) *ᵥ
            (pairVectors (pairParent k)).1) = (pairVectors k.succ).1
          rw [generator_matrix]
          exact (pair_steps k).1
        · rw [map_mul, Module.End.mul_apply, hw]
          change (((generator (pairActor k) : Matrix12ˣ) : Matrix12) *ᵥ
            (pairVectors (pairParent k)).2) = (pairVectors k.succ).2
          rw [generator_matrix]
          exact (pair_steps k).2
  exact hall i.val i.isLt

theorem candidate_card_gt_half : 129 ≤ Nat.card candidate := by
  choose f hf hfv hfw using pairs_reached
  let e : Fin 129 → candidate := fun i => ⟨f i, hf i⟩
  have hinj : Function.Injective e := by
    intro i j h
    have hh : f i = f j := congrArg Subtype.val h
    apply pairVectors_injective
    apply Prod.ext
    · rw [← hfv, ← hfv, hh]
    · rw [← hfw, ← hfw, hh]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective e hinj

theorem candidate_card_lower : 256 ≤ Nat.card candidate := by
  obtain ⟨n, hn⟩ := candidate_isPGroup.exists_card_eq
  have hlo : 2 ^ 7 < 2 ^ n := by rw [← hn]; exact candidate_card_gt_half
  have hn8 : 8 ≤ n := by
    have h := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlo
    omega
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn8

theorem candidate_isSylow : ∃ T : Sylow 2 Group, (T : Subgroup Group) = candidate := by
  obtain ⟨T, hT⟩ := candidate_isPGroup.exists_le_sylow
  have hc : Nat.card T = 256 := by
    rw [T.card_eq_multiplicity, group_card]
    decide +kernel
  exact ⟨T, (Subgroup.eq_of_le_of_card_ge hT (by rw [hc]; exact candidate_card_lower)).symm⟩

end SylowCertificates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
