module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Parabolics
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups

/-!
# The generating binary parabolics in E.6.8

The two five-dimensional partial flags retain complementary pairs of cuts,
so their common Sylow flag and flag-overgroup exhaustion prove generation.
Inverse transpose reverses the cuts and preserves each pair. In dimension
four the line and hyperplane stabilizers generate by the incident-flag
overgroup theorem, and inner automorphisms preserving the full flag fix them.

For characteristic two, the radical at any retained cut lies in every
stabilizer in the nested flag. It is normalized by the partial-flag group
and is self-centralizing in the full binary linear group. Thus the actual
partial-flag stabilizer has a self-centralizing two-core, also for paired cuts.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory BinaryLinear BinaryLinear.OuterCyclic
open BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

private theorem radical_le_comparable {n : ℕ} {W D : Submodule (ZMod 2) (Space n)}
    (h : W ≤ D ∨ D ≤ W) : radical W ≤ parabolic D := by
  intro g hg v
  rcases h with h | h
  · constructor
    · intro hv
      simpa using D.sub_mem hv (h (hg.2 v))
    · intro hv
      simpa using D.add_mem (h (hg.2 v)) hv
  · constructor
    · intro hv
      have he := hg.1 (g v) (h hv)
      have he' : g v = v := g.injective he
      simpa only [he'] using hv
    · intro hv
      simpa only [hg.1 v (h hv)] using hv

/-- Every nonempty binary partial flag has characteristic two. -/
private theorem cutStabilizer_characteristicTwo {m : ℕ} (b : Basis m)
    (cuts : Set (Fin m)) (hne : cuts.Nonempty) :
    HasCharacteristicTwo (cutStabilizer b cuts) := by
  obtain ⟨i, hi⟩ := hne
  apply centralizer_pCore_le_of_normalized 2 (radical (cutSpace b i))
    (cutStabilizer b cuts) (radical_two _)
  · intro g hg
    apply (mem_cutStabilizer b cuts g).mpr
    intro j _
    exact radical_le_comparable
      ((le_total i j).imp (fun h => cutSpace_mono b h) (fun h => cutSpace_mono b h)) hg
  · intro g hg
    exact parabolic_le_normalizer _ ((mem_cutStabilizer b cuts g).mp hg i hi)
  · exact centralizer_radical_le (cutSpace_ne_bot b i) (cutSpace_ne_top b i)

theorem fivePairedParabolic_characteristicTwo (b : FiveFlagGeometry.FiveBasis) (i : Fin 2) :
    HasCharacteristicTwo (fivePairedParabolic b i) := by
  change HasCharacteristicTwo (cutStabilizer b (if i = 0 then {0, 3} else {1, 2}))
  apply cutStabilizer_characteristicTwo
  split <;> simp

theorem fourEndParabolic_characteristicTwo (b : Basis 3) (i : Fin 2) :
    HasCharacteristicTwo (fourEndParabolic b i) := by
  exact centralizer_parabolic_twoCore_le (cutSpace_ne_bot b _) (cutSpace_ne_top b _)

/-- Diagram reversal preserves either paired five-dimensional flag. -/
theorem fivePairedParabolic_invariant (b : FiveFlagGeometry.FiveBasis)
    (a : MulAut (LinearGroup 5))
    (ha : (FiveFlagGeometry.flagStabilizer b Set.univ).map a.toMonoidHom =
      FiveFlagGeometry.flagStabilizer b Set.univ) (i : Fin 2) :
    (fivePairedParabolic b i).map a.toMonoidHom = fivePairedParabolic b i := by
  obtain ⟨g, rfl | rfl⟩ := OuterCyclic.inner_graph (Or.inr rfl) a
  · exact inner_fixes_cutStabilizer b g ha _
  · let cuts : Set (Fin 4) := if i = 0 then {0, 3} else {1, 2}
    have hr (j : Fin 4) : j.rev ∈ cuts ↔ j ∈ cuts := by
      dsimp [cuts]
      split <;> fin_cases j <;> decide
    have hp (j : Fin 4) : (parabolic (cutSpace b j)).map
        (graphLinear 5 * MulAut.conj g).toMonoidHom = parabolic (cutSpace b j.rev) := by
      rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g ha]
    ext s
    change s ∈ (cutStabilizer b cuts).map (graphLinear 5 * MulAut.conj g).toMonoidHom ↔
      s ∈ cutStabilizer b cuts
    rw [mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
    have hm (j : Fin 4) : (graphLinear 5 * MulAut.conj g).symm s ∈ parabolic (cutSpace b j) ↔
        s ∈ parabolic (cutSpace b j.rev) := by
      rw [← hp j, mem_map_equiv]
    constructor
    · intro hs j hj
      change s ∈ parabolic (cutSpace b j)
      simpa only [Fin.rev_rev] using (hm j.rev).mp (hs j.rev ((hr j).mpr hj))
    · intro hs j hj
      exact (hm j).mpr (hs j.rev ((hr j).mpr hj))

theorem fourEndParabolic_invariant (b : Basis 3) (a : MulAut (LinearGroup 4))
    (ha : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ)
    (hi : a ∈ MulAut.innerSubgroup (LinearGroup 4)) (i : Fin 2) :
    (fourEndParabolic b i).map a.toMonoidHom = fourEndParabolic b i := by
  obtain ⟨g, rfl⟩ := hi
  have he : fourEndParabolic b i = cutStabilizer b {if i = 0 then 0 else 2} := by
    simp [fourEndParabolic, cutStabilizer]
  rw [he]
  exact inner_fixes_cutStabilizer b g ha _

/-- The two complementary paired flags generate GL₅(2). -/
theorem fivePairedParabolic_generate (b : FiveFlagGeometry.FiveBasis)
    (S : Sylow 2 (LinearGroup 5))
    (hS : (S : Subgroup _) = FiveFlagGeometry.flagStabilizer b Set.univ) :
    (⨆ i, fivePairedParabolic b i) = ⊤ := by
  let P := ⨆ i, fivePairedParabolic b i
  have hBP : FiveFlagGeometry.flagStabilizer b Set.univ ≤ P :=
    (FiveFlagGeometry.flagStabilizer_antitone b (Set.subset_univ _)).trans
      (le_iSup (fun i => fivePairedParabolic b i) 0)
  obtain ⟨c, cuts, hc⟩ := FiveFlagGeometry.isFlagParabolic_of_sylow_le S P (hS ▸ hBP)
  have he : P = cutStabilizer b cuts := hc.trans (cutStabilizer_eq_of_fullFlag_le b c cuts (by change FiveFlagGeometry.flagStabilizer b Set.univ ≤ FiveFlagGeometry.flagStabilizer c cuts; rw [← hc]; exact hBP))
  have h0 : cuts ⊆ ({0, 3} : Set (Fin 4)) :=
    (cutStabilizer_le_iff b {0, 3} cuts).mp (by
      change fivePairedParabolic b 0 ≤ cutStabilizer b cuts
      rw [← he]
      exact le_iSup (fun i => fivePairedParabolic b i) 0)
  have h1 : cuts ⊆ ({1, 2} : Set (Fin 4)) :=
    (cutStabilizer_le_iff b {1, 2} cuts).mp (by
      change fivePairedParabolic b 1 ≤ cutStabilizer b cuts
      rw [← he]
      exact le_iSup (fun i => fivePairedParabolic b i) 1)
  have hn : cuts = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have := h0 hj
    have := h1 hj
    fin_cases j <;> simp_all
  change P = ⊤
  rw [he, hn]
  simp [cutStabilizer]

private theorem four_cut_zero (b : Basis 3) :
    cutSpace b 0 = Submodule.span (ZMod 2) {b 0} := by
  unfold cutSpace
  have he : {j : Fin 4 | j.val ≤ (0 : Fin 3).val} = {0} := by
    ext j
    simp only [Set.mem_ofPred_eq, Fin.val_zero, Nat.le_zero, Set.mem_singleton_iff]
    exact (Fin.ext_iff (a := j) (b := (0 : Fin 4))).symm
  rw [he, Set.image_singleton]

private theorem four_cut_last (b : Basis 3) : cutSpace b 2 = LinearMap.ker (b.coord 3) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi3 : i ≠ 3 := by intro he; subst i; change 3 ≤ 2 at hi; omega
    simp [LinearMap.mem_ker, Module.Basis.coord_apply, hi3.symm]
  · intro v hv
    rw [← b.sum_repr v]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i = 3
    · subst i
      have hz : b.repr v 3 = 0 := hv
      simp [hz]
    · apply Submodule.smul_mem
      apply (basis_mem_cutSpace b 2 i).mpr
      have : i.val ≠ 3 := fun h => hi (Fin.ext h)
      change i.val ≤ 2
      omega

/-- The line and hyperplane stabilizers generate GL₄(2). -/
theorem fourEndParabolic_generate (b : Basis 3) : (⨆ i, fourEndParabolic b i) = ⊤ := by
  let P := ⨆ i, fourEndParabolic b i
  by_contra hn
  have h0 : fourEndParabolic b 0 ≤ P := le_iSup (fun i => fourEndParabolic b i) 0
  have h1 : fourEndParabolic b 1 ≤ P := le_iSup (fun i => fourEndParabolic b i) 1
  have he0 : fourEndParabolic b 0 = parabolic (Submodule.span (ZMod 2) {b 0}) := by
    simp [fourEndParabolic, four_cut_zero]
  have he1 : fourEndParabolic b 1 = parabolic (LinearMap.ker (b.coord 3)) := by
    simp [fourEndParabolic, four_cut_last]
  have hcover := FourCentralizerOvergroups.flag_overgroup_cover (b 0) (b.coord 3)
    (by simp [Module.Basis.coord_apply]) P (inf_le_left.trans (he0 ▸ h0)) hn
  have hs0 : fourEndParabolic b 0 = cutStabilizer b {0} := by simp [fourEndParabolic, cutStabilizer]
  have hs1 : fourEndParabolic b 1 = cutStabilizer b {2} := by simp [fourEndParabolic, cutStabilizer]
  rcases hcover with hc | hc
  · rw [← he0] at hc
    have hh := h1.trans hc
    rw [hs0, hs1, cutStabilizer_le_iff] at hh
    have := hh (show (0 : Fin 3) ∈ ({0} : Set (Fin 3)) by simp)
    simp at this
  · rw [← he1] at hc
    have hh := h0.trans hc
    rw [hs0, hs1, cutStabilizer_le_iff] at hh
    have := hh (show (2 : Fin 3) ∈ ({2} : Set (Fin 3)) by simp)
    simp at this

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
