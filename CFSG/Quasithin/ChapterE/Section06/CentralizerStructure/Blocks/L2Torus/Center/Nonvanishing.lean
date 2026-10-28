module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Regular
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Fixed

/-!
# From a fixed root-line preimage to nonzero displacement

If the actual preimage in U(L) of the natural root-fixed line is S-fixed,
a lift of (1,0) belongs to Ω₁(Z(S)). It cannot be torus-fixed: on U(L),
torus-fixed elements lie in C_U(L) and have zero natural image. Therefore
the displacement is nontrivial and has order |F|.

The root-line lifting premise is explicit. Its proof must construct the
actual cover and apply the genuine covering theorem I.2.3(3); this module
does not identify that premise with I.2.3 or claim to prove it.
Source: Aschbacher–Smith, printed pp.246 and 413.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {L F : Type*} [Group L] [Field F] [Finite F] [CharP F 2]
    {B : Subgroup L} {a : MarkedBlockModel L B F}

omit [CharP F 2] in
/-- A genuine fixed lift of the root line forces nonzero displacement. -/
theorem DiagonalSection.displacement_ne_bot_of_rootLine_fixed (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hroot : a.rootLine ≤ centralizer (S : Set L)) :
    ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ ≠ ⊥ := by
  let : IsElementaryAbelian 2 (ChapterC.blockU L) := hshort.elementary
  obtain ⟨v, hv⟩ := a.naturalMap_surjective (Multiplicative.ofAdd ![1, 0])
  have hvroot : (v : L) ∈ a.rootLine := by
    apply (a.mem_rootLine _).mpr
    refine ⟨v.property, ?_⟩
    change (a.naturalMap v).toAdd 1 = 0
    rw [hv]
    rfl
  have hvZ : (v : L) ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup L) := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨pCore_isPGroup.le_sylow_of_normal S (ChapterC.blockU_le_core v.property),
      elemPow_eq_one_of_isElementaryAbelian (v : L) v.property,
      mem_centralizer_iff.mp (hroot hvroot)⟩
  intro hbot
  have hvX := commutator_eq_bot_iff_le_centralizer.mp hbot hvZ
  have hvcenter : (v : L) ∈ center L :=
    ((d.blockU_fixed_eq_center hn hF).le ⟨v.property, hvX⟩).2
  have he := (a.naturalMap_eq_one v).mpr hvcenter
  rw [hv] at he
  exact one_ne_zero (congrFun (congrArg Multiplicative.toAdd he) 0)

/-- Conditional order calculation; the cover's fixed-lift premise remains visible. -/
theorem DiagonalSection.displacement_card_of_rootLine_fixed [Finite L]
    (d : DiagonalSection a) (hshort : ChapterC.IsShort L)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hroot : a.rootLine ≤ centralizer (S : Set L)) :
    Nat.card ↥⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ = 2 ^ n :=
  d.displacement_card_of_ne_bot hshort S hS hn hF
    (d.displacement_ne_bot_of_rootLine_fixed hshort S hn hF hroot)

end CFSG.Quasithin.ChapterE.Section06.L2Torus
