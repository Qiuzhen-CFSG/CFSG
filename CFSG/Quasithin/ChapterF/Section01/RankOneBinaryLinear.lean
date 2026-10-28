module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.SpecificGroups.BinaryLinear.SylowNormalizerCover

/-!
# Source rank-one models are not higher-dimensional binary linear groups

In binary dimension at least three, a minimal flag parabolic is a proper
subgroup strictly above a full Sylow two-subgroup. That Sylow is
self-normalizing. This contradicts the unique maximal Sylow-normalizer
property proved for every actual model in F.1.1, including the small and
special-unitary alternatives. No order computation or simplicity premise
is needed.

The consumer is the binary-linear containing-component exclusion in the
smaller changed-Sylow branch of original 5.2.2.
Source: Aschbacher–Smith F.1.1–3 and 5.2.2, printed pp.259–260,648–649
(`refs/quasithin.pdf`). Binary flag results retain LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.SylowFlagOvergroups
namespace CFSG.Quasithin.ChapterF.Source
variable {X : Type*} [Group X]

/-- The actual source rank-one quotient cannot be a binary general linear
group of dimension at least three. -/
theorem IsRankOneModel.not_binary_linear (h : IsRankOneModel X)
    {n : ℕ} (hn : 3 ≤ n) (e : X ≃* LinearGroup n) : False := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  let S : Sylow 2 (LinearGroup (m+1)) := Sylow.nonempty.some
  have hf : RankOneSylowFacts S := rankOneSylowFacts_of_equiv S e.symm (h.rankOneSylowFacts _)
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  let i : Fin m := ⟨0,by omega⟩
  let j : Fin m := ⟨1,by omega⟩
  have hcov := fullFlag_covBy_minimalParabolic S b hb i
  have htop : cutStabilizer b ∅ = ⊤ := by
    ext g
    simp [mem_cutStabilizer]
  have hproper : minimalParabolic b i < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hh : cutStabilizer b ∅ ≤ cutStabilizer b {i}ᶜ := by rw [htop]; exact he.ge
    have hj := (cutStabilizer_le_iff b _ _).mp hh (show j ∈ ({i}ᶜ : Set (Fin m)) from by
      change j ≠ i
      intro hji
      have := congrArg Fin.val hji
      norm_num [i,j] at this)
    exact hj
  have hh := hf.unique_maximal _ hcov.le hproper
  rw [BinaryLinear.SylowNormalizerCover.normalizer_sylow_eq] at hh
  exact hcov.lt.not_ge hh
end CFSG.Quasithin.ChapterF.Source
