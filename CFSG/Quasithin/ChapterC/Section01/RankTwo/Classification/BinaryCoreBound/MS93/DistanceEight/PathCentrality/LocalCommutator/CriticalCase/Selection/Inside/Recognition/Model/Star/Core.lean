module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Model.Basic
/-!
# Pointwise fixation of the common orbit core

If a seed differs from its common orbit core, simplicity forces every
nonidentity actor to move some translate. For the specified involution this
translate escapes its marked stabilizer, so its displacement has order at most
two and contains an element outside the core. Its intersection with the core
is therefore trivial. The involution fixes the core, and simplicity promotes
this to fixation by the entire group.

This proves the core step in the index-two branch of MS93 (1.6), printed
pp.845–847. It does not identify fixation of the core with fixation of the seed.
-/

@[expose] public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [Group E]

private def seedStabilizer (ρ : SL →* MulAut E) (W : Subgroup E) : Subgroup SL :=
  (MulAction.stabilizer (MulAut E) W).comap ρ

private theorem map_conjugate (ρ : SL →* MulAut E) (W : Subgroup E) (g t : SL) :
    ((actionConjugate ρ W g).map (ρ t).toMonoidHom).map (ρ g).toMonoidHom =
      W.map (ρ (g * t * g⁻¹)).toMonoidHom := by
  simp only [actionConjugate, map_map]
  congr 1
  ext w
  simp

private theorem map_conjugate_cancel (ρ : SL →* MulAut E) (W : Subgroup E) (g : SL) :
    (actionConjugate ρ W g).map (ρ g).toMonoidHom = W := by
  have h := actionConjugate_mul ρ W g g⁻¹
  rw [mul_inv_cancel, actionConjugate_one] at h
  simpa only [actionConjugate, inv_inv] using h

private theorem translated_invariant (ρ : SL →* MulAut E)
    (d : EscapingConfiguration ρ) (g t : SL)
    (ht : t ∈ NormalizerTransfer.rightConjugate
      (markedPointStabilizer d.marking d.point) g) :
    (actionConjugate ρ d.seed g).map (ρ t).toMonoidHom = actionConjugate ρ d.seed g := by
  apply Subgroup.map_injective (f := (ρ g).toMonoidHom) (ρ g).injective
  rw [map_conjugate, map_conjugate_cancel]
  obtain ⟨k, hk, rfl⟩ := ht
  convert d.invariant k hk using 2; simp [mul_assoc]

private theorem exists_moved_translate (ρ : SL →* MulAut E)
    (W : Subgroup E) (hproper : actionOrbitCore ρ W ≠ W) (t : SL) (ht : t ≠ 1) :
    ∃ g : SL, (actionConjugate ρ W g).map (ρ t).toMonoidHom ≠ actionConjugate ρ W g := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let H := seedStabilizer ρ W
  have hn : H.normalCore = ⊥ := by
    rcases H.normalCore_normal.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply hproper
      apply le_antisymm (actionOrbitCore_le ρ W)
      apply le_iInf
      intro g
      have hg : g⁻¹ ∈ H := H.normalCore_le (h ▸ mem_top _)
      change W.map (ρ g⁻¹).toMonoidHom = W at hg
      change W ≤ W.map (ρ g⁻¹).toMonoidHom
      exact hg.ge
  by_contra! he
  have htH : t ∈ H.normalCore := by
    intro g
    change W.map (ρ (g * t * g⁻¹)).toMonoidHom = W
    rw [← map_conjugate, he, map_conjugate_cancel]
  exact ht (by simpa only [hn, mem_bot] using htH)

private theorem exists_difference_outside_core (ρ : SL →* MulAut E)
    (W : Subgroup E) (g t : SL) (ht : t ^ 2 = 1)
    (hmoved : (actionConjugate ρ W g).map (ρ t).toMonoidHom ≠ actionConjugate ρ W g) :
    ∃ w ∈ actionConjugate ρ W g, w⁻¹ * ρ t w ∉ actionOrbitCore ρ W := by
  by_contra! he
  have hcore : actionOrbitCore ρ W ≤ actionConjugate ρ W g := iInf_le _ g
  have hstable (w : E) (hw : w ∈ actionConjugate ρ W g) :
      ρ t w ∈ actionConjugate ρ W g := by
    simpa using (actionConjugate ρ W g).mul_mem hw (hcore (he w hw))
  apply hmoved
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact hstable w hw
  · intro w hw
    refine ⟨ρ t w, hstable w hw, ?_⟩
    change ρ t (ρ t w) = w
    rw [← MulAut.mul_apply, ← map_mul, ← pow_two, ht, map_one, MulAut.one_apply]

private theorem small_intersection {D C : Subgroup E} [Finite D]
    (hD : Nat.card D ≤ 2) {x : E} (hx : x ∈ D) (hxc : x ∉ C)
    {y : E} (hy : y ∈ D) (hyc : y ∈ C) : y = 1 := by
  have hx1 : x ≠ 1 := by rintro rfl; exact hxc C.one_mem
  have hcard : Nat.card D = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot D).mpr (fun h => hx1 (by simpa only [h, mem_bot] using hx))
    omega
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hcard
  by_contra hy1
  have hxy : (⟨x,hx⟩ : D) = ⟨y,hy⟩ :=
    (hz _ (fun h => hx1 (congrArg Subtype.val h))).trans
      (hz _ (fun h => hy1 (congrArg Subtype.val h))).symm
  have he : x = y := congrArg Subtype.val hxy
  exact hxc (he ▸ hyc)

private def coreFixer (ρ : SL →* MulAut E) (W : Subgroup E) : Subgroup SL :=
  ⨅ w : actionOrbitCore ρ W, (MulAction.stabilizer (MulAut E) (w : E)).comap ρ

private theorem mem_coreFixer (ρ : SL →* MulAut E) (W : Subgroup E) (g : SL) :
    g ∈ coreFixer ρ W ↔ ∀ w ∈ actionOrbitCore ρ W, ρ g w = w := by
  simp only [coreFixer, mem_iInf, mem_comap, MulAction.mem_stabilizer_iff,
    Subtype.forall]
  rfl

private theorem coreFixer_normal (ρ : SL →* MulAut E) (W : Subgroup E) :
    (coreFixer ρ W).Normal := by
  constructor
  intro n hn g
  rw [mem_coreFixer] at hn ⊢
  intro w hw
  have hin : ρ g⁻¹ w ∈ actionOrbitCore ρ W := by
    rw [← actionOrbitCore_map ρ W g⁻¹]
    exact mem_map_of_mem _ hw
  simp only [map_mul, MulAut.mul_apply, hn _ hin]
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

/-- The small escaping displacement fixes the entire common orbit core. -/
theorem orbitCore_fixed_of_ne_seed [Finite E] (ρ : SL →* MulAut E)
    (d : EscapingConfiguration ρ) (hproper : actionOrbitCore ρ d.seed ≠ d.seed) :
    ∀ k : SL, ∀ w ∈ actionOrbitCore ρ d.seed, ρ k w = w := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  obtain ⟨g, hg⟩ := exists_moved_translate ρ d.seed hproper d.involution d.involution_ne_one
  have hescape : d.involution ∉ NormalizerTransfer.rightConjugate
      (markedPointStabilizer d.marking d.point) g :=
    fun he => hg (translated_invariant ρ d g d.involution he)
  have hle : actionConjugate ρ d.seed g ≤
      actionEscapingSpan ρ (markedPointStabilizer d.marking d.point) d.involution d.seed :=
    le_iSup_of_le g (le_iSup_of_le hescape le_rfl)
  obtain ⟨v, hv, hvc⟩ := exists_difference_outside_core ρ d.seed g d.involution d.involution_sq hg
  let D := actionDisplacement ρ (zpowers d.involution)
    (actionEscapingSpan ρ (markedPointStabilizer d.marking d.point) d.involution d.seed)
  have hvD : v⁻¹ * ρ d.involution v ∈ D :=
    subset_closure ⟨d.involution, mem_zpowers _, v, hle hv, rfl⟩
  have ht : d.involution ∈ coreFixer ρ d.seed := by
    rw [mem_coreFixer]
    intro w hw
    have hwD : w⁻¹ * ρ d.involution w ∈ D :=
      subset_closure ⟨d.involution, mem_zpowers _, w,
        hle ((iInf_le _ g : actionOrbitCore ρ d.seed ≤ actionConjugate ρ d.seed g) hw), rfl⟩
    have hwm : ρ d.involution w ∈ actionOrbitCore ρ d.seed := by
      rw [← actionOrbitCore_map ρ d.seed d.involution]
      exact mem_map_of_mem _ hw
    have hz := small_intersection d.small hvD hvc hwD
      ((actionOrbitCore ρ d.seed).mul_mem ((actionOrbitCore ρ d.seed).inv_mem hw) hwm)
    exact (inv_mul_eq_one.mp hz).symm
  have htop : coreFixer ρ d.seed = ⊤ := by
    rcases (coreFixer_normal ρ d.seed).eq_bot_or_eq_top with hb | ht'
    · exact (d.involution_ne_one (by simpa only [hb, mem_bot] using ht)).elim
    · exact ht'
  intro k
  exact (mem_coreFixer ρ d.seed k).mp (htop ▸ mem_top _)

/-- In particular, the index-two star has a core fixed by the whole group. -/
theorem orbitCore_fixed_of_index_two [Finite E] (ρ : SL →* MulAut E)
    (d : EscapingConfiguration ρ) (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2) :
    ∀ k : SL, ∀ w ∈ actionOrbitCore ρ d.seed, ρ k w = w := by
  apply orbitCore_fixed_of_ne_seed ρ d
  intro he
  rw [he, relIndex_self] at hline
  contradiction

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
