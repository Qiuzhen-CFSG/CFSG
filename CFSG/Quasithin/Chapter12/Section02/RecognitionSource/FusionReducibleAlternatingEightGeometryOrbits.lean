module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingEightGeometryModel

/-!
# Restricting outside fusion to complementary eight-core weights

Normalizer conjugation preserves the sizes of the actual L-orbits. Thus
its orbit on a weight-four word has size 70, while its orbit on a word of
weight two or six has size at most 56. Under NoEscape, global conjugacy
preserves these normalizer-orbit sizes by the full-centralizer form of
orbit-stabilizer. The fixed-line theorem excludes the constant word, and
fusion within one weight class already has an L-conjugator. Every remaining
outside pair therefore has weights two and six.

Source: Aschbacher--Smith, 12.2.16, printed pp.799--800, especially (1)--(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open BinaryPermutation ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace AlternatingEightCoreCoordinates
variable (C : AlternatingEightCoreCoordinates L V)

omit [Finite G] in
/-- Normalizer orbits stay within the two complementary weight classes. -/
theorem normalizerOrbit_subset
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G)) (v : V) :
    conjugacyOrbit (normalizer (L : Set G)) (v : G) ⊆
      C.fiber (C.weight v) ∪ C.fiber (8 - C.weight v) := by
  rintro y ⟨m,rfl⟩
  let w : V := ⟨(m : G) * (v : G) * (m : G)⁻¹,
    (mem_normalizer_iff.mp (hMV m.property) v).mp v.property⟩
  have he := (EightCore.equal_size_iff (C.word v) (C.word w)).mp
    (C.normalizer_preserves_size v w m.property rfl)
  change C.weight v = C.weight w ∨ C.weight v + C.weight w = 8 at he
  rcases he with he | he
  · exact Or.inl ((C.mem_fiber w _).mpr he.symm)
  · exact Or.inr ((C.mem_fiber w _).mpr (by omega))

omit [Finite G] in
theorem normalizerOrbit_four
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v : V) (hv : C.weight v = 4) :
    (conjugacyOrbit (normalizer (L : Set G)) (v : G)).ncard = 70 := by
  have he : conjugacyOrbit (normalizer (L : Set G)) (v : G) = C.fiber 4 := by
    apply Set.Subset.antisymm
    · simpa [hv] using C.normalizerOrbit_subset hMV v
    · rw [← hv,← C.orbit_eq_fiber]
      rintro y ⟨l,rfl⟩
      exact ⟨⟨l,L.le_normalizer l.property⟩,rfl⟩
  rw [he,C.fiber_card]
  rfl

theorem normalizerOrbit_two_six_le
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v : V) (hv : C.weight v = 2 ∨ C.weight v = 6) :
    (conjugacyOrbit (normalizer (L : Set G)) (v : G)).ncard ≤ 56 := by
  have hh := (Set.ncard_mono (C.normalizerOrbit_subset hMV v)).trans
    (Set.ncard_union_le _ _)
  rw [C.fiber_card,C.fiber_card] at hh
  rcases hv with hv | hv <;> simpa [hv,EightCore.orbitSize] using hh

/-- Under NoEscape, conjugate points have normalizer orbits of equal size. -/
theorem conjugate_normalizerOrbit_card (hnone : NoEscape L V)
    (v w : V) (hv : (v : G) ≠ 1) (hw : (w : G) ≠ 1)
    {g : G} (hg : g * (v : G) * g⁻¹ = w) :
    (conjugacyOrbit (normalizer (L : Set G)) (v : G)).ncard =
      (conjugacyOrbit (normalizer (L : Set G)) (w : G)).ncard := by
  have hc : Nat.card (centralizer ({(v : G)} : Set G)) =
      Nat.card (centralizer ({(w : G)} : Set G)) := by
    have hh := Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.conj g) (v : G)).toEquiv
    simpa only [MulAut.conj_apply,hg] using hh
  have hcv := conjugacyOrbit_mul_centralizer (normalizer (L : Set G))
    (v : G) (hnone v v.property hv)
  have hcw := conjugacyOrbit_mul_centralizer (normalizer (L : Set G))
    (w : G) (hnone w w.property hw)
  rw [← hc] at hcw
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := centralizer ({(v : G)} : Set G))) (hcv.trans hcw.symm)

/-- The actual source hypotheses force every outside fusion pair into weights two and six. -/
theorem outside_weights
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v w : V) (hv : (v : G) ≠ 1) {g : G}
    (hout : g ∉ normalizer (L : Set G)) (hg : g * (v : G) * g⁻¹ = w) :
    (C.weight v = 2 ∧ C.weight w = 6) ∨ (C.weight v = 6 ∧ C.weight w = 2) := by
  have hw : (w : G) ≠ 1 := fun he => hv ((MulAut.conj g).map_eq_one_iff.mp (hg.trans he))
  have hn : C.weight v ≠ C.weight w := by
    intro he
    obtain ⟨l,hl,he⟩ := C.conjugator_of_weight v w he
    exact hout (conjugator_mem_of_centralizer_le (hnone v v.property hv)
      ⟨l,L.le_normalizer hl,he.trans hg.symm⟩)
  have hvz : v ≠ C.z := by
    intro he
    subst v
    exact hout (conjugator_mem_of_fixed_line_image h D structural hnone C.z.property
      C.z_ne C.z_fixed C.fixed_line (hg ▸ w.property))
  have hwz : w ≠ C.z := by
    intro he
    subst w
    have hi : g⁻¹ * (C.z : G) * (g⁻¹)⁻¹ = v := by rw [← hg]; group
    have hm := conjugator_mem_of_fixed_line_image h D structural hnone C.z.property
      C.z_ne C.z_fixed C.fixed_line (hi ▸ v.property)
    exact hout (by simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem hm)
  have hv0 : C.weight v ≠ 0 := fun he => hv (congrArg Subtype.val ((C.weight_zero_iff v).mp he))
  have hw0 : C.weight w ≠ 0 := fun he => hw (congrArg Subtype.val ((C.weight_zero_iff w).mp he))
  have hv8 : C.weight v ≠ 8 := fun he => hvz ((C.weight_eight_iff v).mp he)
  have hw8 : C.weight w ≠ 8 := fun he => hwz ((C.weight_eight_iff w).mp he)
  have hvw := EightCore.weights (C.word v)
  have hww := EightCore.weights (C.word w)
  change C.weight v = 0 ∨ C.weight v = 2 ∨ C.weight v = 4 ∨
    C.weight v = 6 ∨ C.weight v = 8 at hvw
  change C.weight w = 0 ∨ C.weight w = 2 ∨ C.weight w = 4 ∨
    C.weight w = 6 ∨ C.weight w = 8 at hww
  have hc := conjugate_normalizerOrbit_card hnone v w hv hw hg
  have hv4 : C.weight v ≠ 4 := by
    intro h4
    have hw26 : C.weight w = 2 ∨ C.weight w = 6 := by omega
    have hb := C.normalizerOrbit_two_six_le hMV w hw26
    rw [← hc,C.normalizerOrbit_four hMV v h4] at hb
    omega
  have hw4 : C.weight w ≠ 4 := by
    intro h4
    have hv26 : C.weight v = 2 ∨ C.weight v = 6 := by omega
    have hb := C.normalizerOrbit_two_six_le hMV v hv26
    rw [hc,C.normalizerOrbit_four hMV w h4] at hb
    omega
  omega

end AlternatingEightCoreCoordinates
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
