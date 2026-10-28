module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ModelExclusions
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional.InnerInvolution
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional.ModelCentralizers

/-!+# Excluding the three-dimensional components in E.6.23

The Borel decomposition supplies a noncentral involution of X inside U.
The embedded small block centralizes it, so three divides its centralizer
order. For PSL₃(4), PSU₃(4), and every central two-cover of PSL₃(4), the
actual model calculations contradict that divisibility.

Only the genuine E.6.1 input is added to the published exclusion contract.
The block retains its original A₃/A₅ conjugation module and relative
subnormality; neither relative normality nor a module identification is
assumed. The component-case owner assembles this with the other exclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265), with E.6.8(1) on printed pp.247–248.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open ComponentBalance Components ThreeDimensional

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

private theorem two_group_three_free {D : Type*} [Group D] [Finite D] (hp : IsPGroup 2 D) :
    ¬ 3 ∣ Nat.card D := by
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn]
  exact fun hh => (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) hh)

/-- All three remaining Borel models are excluded, including every central
two-cover, with the unitary parameter interpreted as the fixed-field order. -/
theorem threeDimensionalExclusion [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V) :
    ThreeDimensionalExclusion M V := by
  intro U _ hUh L hL _ A hA hAU hc X hLX hX hfixed b hm
  obtain ⟨t, htU, htZ, ht2⟩ :=
    borel_hyperplane_inner_involution h hUh hA hAU hc hX hfixed b
  have ht : t ≠ 1 := fun hh => htZ (hh ▸ (center X).one_mem)
  have h3 := smallBlock_three_dvd_centralizer hL hLX.le t htU
  rcases hm with hm | hm | ⟨hz, hm⟩
  · exact two_group_three_free (linear_four_centralizer_isTwoGroup hm t ht ht2) h3
  · exact unitary_four_centralizer_three_free hm t ht ht2 h3
  · exact two_group_three_free
      (cover_linear_four_centralizer_isTwoGroup hz hm t htZ ht2) h3

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
