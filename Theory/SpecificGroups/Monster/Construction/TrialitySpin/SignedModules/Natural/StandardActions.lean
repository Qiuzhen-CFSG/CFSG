module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Natural.Actions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Automorphisms

/-!
# Standard automorphisms and transport between the natural modules

The existing standard Parker group supplies the marked Golay coordinate
permutation. Specializing the computed halfspace formulas therefore gives
Lemma 27.4(2) without any extra action assumption. For an odd second
automorphism the first and third axes are interchanged. Both directions are
retained as linear equivalences, with halfspace equations that certify their
actual source and target axes.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.4(2)–(3), printed p. 146
(PDF page 79), and the coordinate permutations of Section 14. The induced
representations of the whole `N1` and their structural kernels belong to the
triality assembly.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin.SignedModules.Natural

/-- This coordinate formula is supplied by the genuine standard automorphism group. -/
theorem standard_coordinates (α : ParkerStandardGroup) (d : ParkerLoop) :
    (α.val d).1.val = coordinatePermutation (parkerStandardProjection α).val d.1.val :=
  congrArg Subtype.val (parkerStandardProjection_spec α d)

/-- Every actual standard automorphism has the computed coordinate-halfspace action. -/
theorem standard_halfspace (i j : Axis) (α : ParkerStandardGroup)
    (x : Omega) (ε : ParkerBit) :
    psiAutAt i α.val '' halfspace j (x, ε) =
      halfspace (autTarget i α.val j) ((parkerStandardProjection α).val x, ε) :=
  psiAut_halfspace i j α.val (parkerStandardProjection α).val (standard_coordinates α) x ε

theorem standard_carries (i j : Axis) (α : ParkerStandardGroup) :
    Carries j (autTarget i α.val j) (psiAutAt i α.val) :=
  psiAut_carries i j α.val (parkerStandardProjection α).val (standard_coordinates α)

/-- The natural-module map of a genuine standard automorphism, with its target axis. -/
def standardTransport (i j : Axis) (α : ParkerStandardGroup) :
    Space j ≃ₗ[ℝ] Space (autTarget i α.val j) :=
  transport (psiAutAt i α.val) (standard_carries i j α)

theorem standardTransport_L (i j : Axis) (α : ParkerStandardGroup)
    (x : Omega) (ε : ParkerBit) :
    standardTransport i j α (L j ε x) =
      L (autTarget i α.val j) ε ((parkerStandardProjection α).val x) :=
  psiAut_linear i j α.val (parkerStandardProjection α).val (standard_coordinates α) x ε

@[simp] theorem autTarget_self (i : Axis) (e : Equiv.Perm ParkerLoop) :
    autTarget i e i = i := by
  fin_cases i <;> simp [autTarget, oddAxis]

/-- Source 27.4(2): `ψᵢ(α)` preserves its own halfspace family, for either parity. -/
theorem standard_self_halfspace (i : Axis) (α : ParkerStandardGroup)
    (x : Omega) (ε : ParkerBit) :
    psiAutAt i α.val '' halfspace i (x, ε) =
      halfspace i ((parkerStandardProjection α).val x, ε) := by
  simpa only [autTarget_self] using standard_halfspace i i α x ε

theorem standard_self_carries (i : Axis) (α : ParkerStandardGroup) :
    Carries i i (psiAutAt i α.val) := by
  simpa only [autTarget_self] using standard_carries i i α

theorem standard_self_linear (i : Axis) (α : ParkerStandardGroup)
    (x : Omega) (ε : ParkerBit) :
    transport (psiAutAt i α.val) (standard_self_carries i α) (L i ε x) =
      L i ε ((parkerStandardProjection α).val x) := by
  rw [transport_L, labelEquiv_of_image _ _ _ _ (standard_self_halfspace i α x ε)]

/-- An even standard automorphism preserves all three halfspace families. -/
theorem standard_even_halfspace (i j : Axis) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (ε : ParkerBit) :
    psiAutAt i α.val '' halfspace j (x, ε) =
      halfspace j ((parkerStandardProjection α).val x, ε) := by
  simpa only [autTarget, if_pos hα] using standard_halfspace i j α x ε

/-- Source 27.4(3): an odd second automorphism carries axis 1 to axis 3. -/
theorem psiAut2_odd_halfspace1 (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x : Omega) (ε : ParkerBit) :
    psiAut2 α.val '' halfspace 0 (x, ε) =
      halfspace 2 ((parkerStandardProjection α).val x, ε) := by
  simpa only [psiAutAt, autTarget, if_neg hα, oddAxis] using standard_halfspace 1 0 α x ε

/-- The reverse-axis counterpart: the same odd permutation carries axis 3 to axis 1. -/
theorem psiAut2_odd_halfspace3 (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x : Omega) (ε : ParkerBit) :
    psiAut2 α.val '' halfspace 2 (x, ε) =
      halfspace 0 ((parkerStandardProjection α).val x, ε) := by
  simpa only [psiAutAt, autTarget, if_neg hα, oddAxis] using standard_halfspace 1 2 α x ε

theorem psiAut2_odd_carries1 (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) : Carries 0 2 (psiAut2 α.val) := by
  rintro ⟨x, ε⟩
  exact ⟨_, psiAut2_odd_halfspace1 α hα x ε⟩

theorem psiAut2_odd_carries3 (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) : Carries 2 0 (psiAut2 α.val) := by
  rintro ⟨x, ε⟩
  exact ⟨_, psiAut2_odd_halfspace3 α hα x ε⟩

/-- The source and target of this map are the first and third natural modules. -/
def psiAut2Odd13 (α : ParkerStandardGroup) (hα : α.val parkerOmega ≠ parkerOmega) :
    B1_24 ≃ₗ[ℝ] B3_24 := transport (psiAut2 α.val) (psiAut2_odd_carries1 α hα)

/-- The counterpart has source the third natural module and target the first. -/
def psiAut2Odd31 (α : ParkerStandardGroup) (hα : α.val parkerOmega ≠ parkerOmega) :
    B3_24 ≃ₗ[ℝ] B1_24 := transport (psiAut2 α.val) (psiAut2_odd_carries3 α hα)

theorem psiAut2Odd13_L (α : ParkerStandardGroup) (hα : α.val parkerOmega ≠ parkerOmega)
    (x : Omega) (ε : ParkerBit) :
    psiAut2Odd13 α hα (L 0 ε x) = L 2 ε ((parkerStandardProjection α).val x) := by
  unfold psiAut2Odd13
  rw [transport_L, labelEquiv_of_image _ _ _ _ (psiAut2_odd_halfspace1 α hα x ε)]

theorem psiAut2Odd31_L (α : ParkerStandardGroup) (hα : α.val parkerOmega ≠ parkerOmega)
    (x : Omega) (ε : ParkerBit) :
    psiAut2Odd31 α hα (L 2 ε x) = L 0 ε ((parkerStandardProjection α).val x) := by
  unfold psiAut2Odd31
  rw [transport_L, labelEquiv_of_image _ _ _ _ (psiAut2_odd_halfspace3 α hα x ε)]

end Sporadic.Monster.Construction.TrialitySpin.SignedModules.Natural
