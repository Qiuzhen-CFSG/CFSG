module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.Recovery
public import Theory.Representation.BinaryOffender.CubicIrreducibleSection
public import Theory.Representation.RepEquiv
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Reduced recovery from the source triple-six section

This version retains only the cubic center and section dimension from the
triple-six action. It does not assert an offender-line clause.

`SelectedSection` records the remaining branch-selection output of B.5.1;
this module does not assert its existence from the source alternatives.
Once that branch is selected, full commutator generation makes its moved
space the original module. The actual central projection is injective by
the central cubic norm argument, without a splitting assumption. Thus the
section's irreducibility and dimension six hold on the original module.

Source: Aschbacher–Smith, B.5.1, printed p.99, and the final proof of 15.3.1,
printed p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- A selected B.5.1(1i)/B.4.2(8) branch on its literal moved central section.
Existence and the equality of the component with the actor are obligations of
branch selection, not assumptions added to the original source theorem. -/
structure SelectedSection (ρ : Representation (ZMod 2) D W) (L : Subgroup D) where
  sectionData : MovedSection ρ L
  whole : L = ⊤
  faithful : Function.Injective sectionData.action
  irreducible : IsIrreducible (sectionData.action.comp L.subtype)
  centerEquiv : center L ≃* Multiplicative (ZMod 3)
  dimension : Module.finrank (ZMod 2)
    (sectionData.space.toSubmodule ⧸ sectionData.central.toSubmodule) = 6

/-- Forget the legacy offender clause; the section and every action map remain literal. -/
noncomputable def SelectedSection.ofLegacy
    {ρ : Representation (ZMod 2) D W} {L : Subgroup D}
    (s : CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SelectedSection ρ L) :
    SelectedSection ρ L where
  sectionData := s.sectionData
  whole := s.whole
  faithful := s.faithful
  irreducible := s.irreducible
  centerEquiv := s.tripleSix.centerEquiv
  dimension := s.tripleSix.dimension

/-- The corrected projective-line branch supplies exactly the reduced recovery data. -/
noncomputable def SelectedSection.ofProjectiveLine
    {ρ : Representation (ZMod 2) D W} {L : Subgroup D}
    (s : MovedSection ρ L) (hwhole : L = ⊤)
    (hf : Function.Injective s.action)
    (hi : IsIrreducible (s.action.comp L.subtype))
    (a : ProjectiveLine.TripleSixAction s.action L) : SelectedSection ρ L where
  sectionData := s
  whole := hwhole
  faithful := hf
  irreducible := hi
  centerEquiv := a.centerEquiv
  dimension := a.dimension

namespace SelectedSection
variable {ρ : Representation (ZMod 2) D W} {L : Subgroup D}
  (s : SelectedSection ρ L) (hm : moved ρ ⊤ = ⊤)

include hm in
/-- Full commutator generation removes any ambient fixed summand. -/
theorem space_eq_top : s.sectionData.space.toSubmodule = ⊤ := by
  rw [s.sectionData.space_eq, s.whole, hm]

/-- The literal inclusion into the moved space followed by central projection. -/
noncomputable def projection : W →ₗ[ZMod 2]
    (s.sectionData.space.toSubmodule ⧸ s.sectionData.central.toSubmodule) :=
  s.sectionData.central.toSubmodule.mkQ.comp
    (LinearEquiv.ofTop s.sectionData.space.toSubmodule (s.space_eq_top hm)).symm.toLinearMap

/-- Both maps defining the projection are surjective. -/
theorem projection_surjective : Function.Surjective (s.projection hm) :=
  s.sectionData.central.toSubmodule.mkQ_surjective.comp
    (LinearEquiv.ofTop s.sectionData.space.toSubmodule (s.space_eq_top hm)).symm.surjective

/-- The projection respects the whole original actor. -/
theorem projection_intertwines (g : D) (v : W) :
    s.projection hm (ρ g v) = (MovedSection.action ρ s.sectionData) g (s.projection hm v) := rfl

/-- The selected section is irreducible for the whole actor. -/
theorem action_isIrreducible : IsIrreducible s.sectionData.action := by
  let e : L ≃* D := (MulEquiv.subgroupCongr s.whole).trans Subgroup.topEquiv
  exact RepEquiv.irreducible_of_group_iso e (fun _ _ => rfl) s.irreducible

/-- The central cubic element rules out a hidden nonsplit fixed kernel. -/
theorem projection_injective : Function.Injective (s.projection hm) := by
  let z : center L := s.centerEquiv.symm (Multiplicative.ofAdd (1 : ZMod 3))
  have hz : (z : L) ≠ 1 := by
    intro h
    have hz' : z = 1 := Subtype.ext h
    have he := congrArg s.centerEquiv hz'
    simp [z] at he
  have hcard : Nat.card (center L) = 3 := by
    rw [Nat.card_congr s.centerEquiv.toEquiv]
    simp
  let : Finite (center L) := Finite.of_equiv _ s.centerEquiv.symm.toEquiv
  have hz3 : (z : L) ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := z)
    rw [hcard] at h
    exact congrArg Subtype.val h
  apply injective_of_central_cubic_irreducible_target
    (ρ.comp L.subtype) (s.sectionData.action.comp L.subtype) (s.projection hm)
    (fun g v => s.projection_intertwines hm g v) ?_ ?_
    s.irreducible (s.faithful.comp Subtype.val_injective) (z : L) z.property hz hz3
  · intro v hv g
    have hc : (LinearEquiv.ofTop s.sectionData.space.toSubmodule (s.space_eq_top hm)).symm v ∈
        s.sectionData.central.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hv
    rw [s.sectionData.central_eq] at hc
    exact congrArg Subtype.val (hc g.val)
  · apply top_unique
    conv_lhs => rw [← hm]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    exact Submodule.subset_span
      ⟨⟨g, s.whole.symm ▸ mem_top g⟩, mem_top _, v, Submodule.mem_top, rfl⟩

/-- The original module is identified with the literal selected section. -/
noncomputable def originalEquiv : W ≃ₗ[ZMod 2]
    (s.sectionData.space.toSubmodule ⧸ s.sectionData.central.toSubmodule) :=
  LinearEquiv.ofBijective (s.projection hm)
    ⟨s.projection_injective hm, s.projection_surjective hm⟩

include s hm in
/-- Dimension six belongs to the original module, not only its section. -/
theorem finrank_eq_six : Module.finrank (ZMod 2) W = 6 :=
  (s.originalEquiv hm).finrank_eq.trans s.dimension

include s hm in
/-- Irreducibility lifts through the proved central projection equivalence. -/
theorem original_isIrreducible : IsIrreducible ρ := by
  let e : RepEquiv ρ s.sectionData.action :=
    ⟨s.originalEquiv hm, fun g => LinearMap.ext (s.projection_intertwines hm g)⟩
  exact RepEquiv.irreducible_of_euqiv e s.action_isIrreducible

include hm in
/-- The fixed kernel of the selected moved section actually vanishes. -/
theorem central_eq_bot : s.sectionData.central.toSubmodule = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  apply Subtype.ext
  change (v : W) = 0
  apply s.projection_injective hm
  change s.sectionData.central.toSubmodule.mkQ _ = s.projection hm 0
  rw [map_zero]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact hv

end SelectedSection
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter
