module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.Source

/-!
# From individual dual-pairing values to subgroup bounds

The source theorem gives the same fixed subgroup as the commutator value
for every noncentral element of C_W(X). Applying it to generators bounds
the commutator with any subgroup of C_W(X). A single noncentral element
in a second such subgroup identifies the whole value subgroup, allowing
comparison of the two commutators.

This is a genuine application of (1.7)(ii), with all its SourceData and
its additional natural-centralizer-factor hypothesis retained explicitly.
It does not construct those inputs in the amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(ii), pp.847--848,
and its last use in (4.3.2), p.886.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
open RankOnePairing

theorem subgroup_bound {A : Type*} [Group A] [Finite A]
    {e : Extension (M := A)} {i : Bool} {Z W X D : Subgroup A}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set A) = ⊥)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set A)))
    (hD : D ≤ W ⊓ centralizer (X : Set A)) :
    ⁅generated X, D⁆ ≤ Z ⊓ centralizer (localCore (localParabolic e i) : Set A) := by
  have hv := (theorem_1_7_ii d h n).2
  apply commutator_le.mpr
  intro u hu w hw
  by_cases hc : w ∈ centralizer (generated X : Set A)
  · have he : ⁅u, w⁆ = 1 := by
      rw [commutatorElement_def]
      have hcomm := hc u hu
      rw [hcomm]
      group
    rw [he]
    exact one_mem _
  · have he := hv ⟨w, hD hw⟩ hc
    rw [← he]
    exact commutator_mem_commutator hu (mem_zpowers w)

theorem subgroup_value {A : Type*} [Group A] [Finite A]
    {e : Extension (M := A)} {i : Bool} {Z W X D : Subgroup A}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set A) = ⊥)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set A)))
    (hD : D ≤ W ⊓ centralizer (X : Set A))
    (hn : ⁅generated X, D⁆ ≠ ⊥) :
    ⁅generated X, D⁆ = Z ⊓ centralizer (localCore (localParabolic e i) : Set A) := by
  apply le_antisymm (subgroup_bound d h n hD)
  have hout : ¬ D ≤ centralizer (generated X : Set A) := by
    intro hd
    apply hn
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hd
  obtain ⟨w, hw, hc⟩ := SetLike.not_le_iff_exists.mp hout
  rw [← (theorem_1_7_ii d h n).2 ⟨w, hD hw⟩ hc]
  exact commutator_mono le_rfl (zpowers_le.mpr hw)

/-- Compare the pairing on two subgroups centralizing the same source seed.
The second subgroup must give a nonzero pairing. -/
theorem subgroup_comparison {A : Type*} [Group A] [Finite A]
    {e : Extension (M := A)} {i : Bool} {Z W X D E : Subgroup A}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set A) = ⊥)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set A)))
    (hD : D ≤ W ⊓ centralizer (X : Set A))
    (hE : E ≤ W ⊓ centralizer (X : Set A))
    (hn : ⁅generated X, E⁆ ≠ ⊥) : ⁅generated X, D⁆ ≤ ⁅generated X, E⁆ := by
  rw [subgroup_value d h n hE hn]
  exact subgroup_bound d h n hD

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
