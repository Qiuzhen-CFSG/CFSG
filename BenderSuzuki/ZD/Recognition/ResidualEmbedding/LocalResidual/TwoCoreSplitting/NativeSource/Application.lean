module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.NativeSource.Counting
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.NativeSource.LocalConfiguration.Application
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.Application

/-!
# Section 17 splitting from the original selected source configuration

The marked involutions construct the actual odd noncentral subgroup D₀.
Lemma 16.7 gives the exact two-point fixed set and relative normalizer.
The local nonsolvability and trace count identify the genuine covering
models at the original parameter; the counting proof eliminates the
nonlinear alternatives and the completed core-growth argument splits M.

Source: GLS IV, Chapter 2, Lemmas 17.1–17.5 and Proposition 17.6.
Only the preceding Section 16 source inputs remain explicit.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17.NativeSource
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The literal two-core complement required by the final Section 17
argument. All Section 17 configuration, model and counting inputs are
constructed; the displayed assumptions are the preceding source facts. -/
public theorem exists_twoCore_complement_of_selected_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hnM : ¬ IsStronglyEmbedded M)
    (hg : ResidualGeneration Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (h16 : SectionSixteenNormalizer Z M)
    (t : G) (ht : t ∈ Z) (htM : t ∉ M)
    (u : residualPairIn M t) (hu : orderOf u = 2)
    (htu : Commute t ((u : M) : G)) (z : M) (hz : (z : G) ∈ Z)
    (hzu : Commute (z : G) ((u : M) : G))
    (hfusion : IsConj ((u : M) : G) (t * ((u : M) : G)))
    (hns : ¬ Group.IsSolvable
      (localCircle Z (centralizer ({((u : M) : G)} : Set G))))
    (P : Sylow 2 (centralizerClosure Z ((u : M) : G)))
    (hdiv : ((residualCentralizerTrace Z M ((u : M) : G)).ncard + 1) *
      Nat.card P ∣ Nat.card (G ⧸ M) - 1) :
    ∃ t ∈ Z, t ∉ M ∧ (residualPairIn M t).IsComplement' (pCore 2 M) := by
  have hui : PFAppendixIII.IsInvolution ((u : M) : G) := by
    have ho : orderOf ((u : M) : G) = 2 := by simpa using hu
    obtain ⟨hs, hn⟩ := orderOf_eq_prime_iff.mp ho
    exact ⟨hn, hs⟩
  have hC : ¬ centralizer ({((u : M) : G)} : Set G) ≤ M := fun hle =>
    htM (hle (mem_centralizer_singleton_iff.mpr htu.eq))
  obtain ⟨n, _, htrace⟩ := residualCentralizerTrace_ncard_eq_two_pow_sub_one_of_nonsolvable
    h r ha hui (u : M).property hC hns
  have hq : (residualCentralizerTrace Z M ((u : M) : G)).ncard + 1 = 2 ^ n := by
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [hq] at hdiv
  let d := localDataOfSelected h.disconnected r hg t ht htM u hu htu z hz hzu hfusion
  obtain ⟨c⟩ := twoCoreCountingData_of_nonsolvable_trace h r ha hnM hg d hlocal
    hns htrace P hdiv hfusion
    (localData_fixed_pair_iff h.disconnected h16 d)
    (localData_intrinsic_normalizer h.disconnected h16 d)
  exact ⟨c.t, c.t_mem, c.t_not_mem,
    c.isComplement_of_local_cyclicSylow h r ha hnM hg hlocal⟩

end BenderSuzuki.ZD.Section17.NativeSource
