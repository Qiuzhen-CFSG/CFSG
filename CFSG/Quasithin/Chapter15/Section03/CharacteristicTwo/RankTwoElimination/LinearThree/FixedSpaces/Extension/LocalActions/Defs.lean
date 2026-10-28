module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Transport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Alternatives
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Moving

/-!
# Source and moving-layer interfaces for the local L₃(2) action

The source data retain all five complete C.1.34 alternatives in the actual
subgroup LR, with its own Sylow subgroup and quotient marking. In particular,
the six-chief-factor alternative is retained and no normalization by S is
asserted. The moving-layer interface distinguishes one natural copy, two
natural copies with a common marking, and a nonsplit natural cover with its
actual one-dimensional fixed kernel.

These are input and output interfaces for the source reduction, not an
assertion that the local moving representation is an FF-module. The checked
FF classification supplies this output when that additional premise is proved.
Source: Aschbacher–Smith, C.1.34, pp.136–137; B.4.8, pp.91–92;
the first paragraph of 15.3.23, printed p.1128 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
universe u

/-- All five full source cases, on the literal local group LR. -/
structure SourceData {G : Type u} [Group G] (κ : GroupClass.{u}) (L R : Subgroup G) where
  ms : MSPair κ (L ⊔ R : Subgroup G)
    (L.subgroupOf (L ⊔ R : Subgroup G)) (R.subgroupOf (L ⊔ R : Subgroup G))
  sylow : Sylow 2 (L ⊔ R : Subgroup G)
  radical_le : R.subgroupOf (L ⊔ R : Subgroup G) ≤ (sylow : Subgroup (L ⊔ R : Subgroup G))
  quotient : ((L.subgroupOf (L ⊔ R : Subgroup G)) ⧸
    pCore 2 (L.subgroupOf (L ⊔ R : Subgroup G))) ≃* SL
  alternative : Alternatives (ZMod 2) 1 (L.subgroupOf (L ⊔ R : Subgroup G))
    (R.subgroupOf (L ⊔ R : Subgroup G)) sylow quotient

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The three actual possibilities for the moving representation, retaining
coordinates and the exact fixed kernel in the nonsplit case. -/
inductive MovingStructure (ρ : Representation (ZMod 2) SL V) : Prop
  | one (coordinates : Nonempty (Copies (moving ρ).toRepresentation 1))
  | two (coordinates : Nonempty (Copies (moving ρ).toRepresentation 2))
  | nonsplit (quotient : Nonempty (ModuleQuotient (moving ρ).toRepresentation 1))
      (fixed_line : Module.finrank (ZMod 2)
        (fixedSpace (moving ρ).toRepresentation ⊤) = 1)

/-- The established FF theorem produces the full moving description. The
source application must prove the FF property for this precise representation. -/
theorem movingStructure_of_FF [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL V) (hρ : Function.Injective ρ) (hFF : IsFFModule ρ) :
    MovingStructure ρ := by
  rcases moving_trichotomy ρ hρ hFF with ⟨e,_⟩ | ⟨e,_⟩ | ⟨q,h⟩
  · exact .one e
  · exact .two e
  · exact .nonsplit q ((fixedMovingEquiv ρ).finrank_eq.trans h)

/-- Each full moving description supplies the common marked natural quotient
required by the extension calculation. -/
theorem MovingStructure.quotient {ρ : Representation (ZMod 2) SL V}
    (h : MovingStructure ρ) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (ModuleQuotient (moving ρ).toRepresentation m) := by
  cases h with
  | one e => exact ⟨1, Or.inl rfl, ⟨e.some.toQuotient⟩⟩
  | two e => exact ⟨2, Or.inr rfl, ⟨e.some.toQuotient⟩⟩
  | nonsplit q _ => exact ⟨1, Or.inl rfl, q⟩

/-- The nonsplit branch has the source's actual dimension four: its natural
quotient has dimension three and its exact fixed kernel is a line. -/
theorem nonsplit_finrank [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) SL V}
    (q : ModuleQuotient (moving ρ).toRepresentation 1)
    (hline : Module.finrank (ZMod 2) (fixedSpace (moving ρ).toRepresentation ⊤) = 1) :
    Module.finrank (ZMod 2) (moving ρ).toSubmodule = 4 := by
  have h := q.projection.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr q.surjective, finrank_top, q.kernel, hline] at h
  simpa [Module.finrank_pi_fintype] using h.symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
