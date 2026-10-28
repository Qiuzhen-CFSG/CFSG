module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior.SourceFF
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryNatural
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# The complete binary SL₅ source branch

The actual central quotient and the trivial universal covering kernel
recover the original component as SL₅(2). The cubic degree sieve yields
only dimensions five and ten. Full binary linear-image recognition handles
the natural case; the exhaustive exterior recognition and offender
calculation handle the ten-dimensional case. No cover, dimension,
module-identification or offender-classification premise remains.

The direct B.4 application derives the cubic bound from its given best
offender. The earlier source interface with cubic ratio at most two is
preserved and independently supplies the same complete alternatives.

Source: Aschbacher–Smith K.3.2 and B.4.2(9),(11), printed pp.454–455,86.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.SL5TenDimensional
namespace CFSG.Quasithin.ChapterK.Linear.BinaryFiveSource
variable {G V : Type*} [_root_.Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem component_equiv (hq : IsQuasisimple L)
    (hquot : ClassicalGroup.IsPSL (L ⧸ center L) 5 2) : Nonempty (L ≃* Group) := by
  let : IsQuasisimple L := hq
  obtain ⟨F, hField, hFinite, hF, ⟨eQ⟩⟩ := hquot
  let : Field F := hField
  let : Finite F := hFinite
  let j := Theory.SpecificGroups.PSL5Two.UniversalCover.fieldEquiv F hF
  let e := PerfectCentralCovering.centralQuotientEquivOfUniversalKernelEqBot
    Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot (eQ.trans j)
  exact ⟨e.trans projectiveEquiv.symm⟩

theorem actionCase_of_source (h : RankOne.SourceHypotheses ρ L)
    (hquot : ClassicalGroup.IsPSL (L ⧸ center L) 5 2) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  let h' : Recognition.SourceHypothesis KnownSimple.IsKnownSimple ρ L :=
    ⟨inferInstance, inferInstance, h.sqtk, h.fitting, h.quasisimple,
      h.faithful, h.irreducible, h.smallCubic⟩
  obtain ⟨e⟩ := component_equiv h.quasisimple hquot
  rcases Recognition.BinaryCubicSieve.five_degrees h' e with h5 | h10
  · exact Recognition.BinaryNatural.actionCase_of_finrank h 5 (Or.inr rfl) e h5
  · exact Exterior.SourceFF.actionCase_of_finrank h' e h10

theorem actionCase_of_bestOffender
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple G) (hfit : L = generalizedFitting G)
    (hquasi : IsQuasisimple L) (hfaith : Function.Injective ρ)
    (hirr : IsIrreducible (ρ.comp L.subtype))
    (hquot : ClassicalGroup.IsPSL (L ⧸ center L) 5 2)
    (A : Subgroup G) (hA : IsBestOffender ρ A) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have hff : IsFFModule ρ := ⟨A, hA.isOffender ρ⟩
  have hc : cubicRatio ρ ≤ 2 :=
    ((isFFModule_iff_cubicRatio_le_one ρ).mp hff).trans (by norm_num)
  exact actionCase_of_source ⟨hsqtk, hfit.symm, hquasi, hfaith, hirr, hc⟩ hquot

end CFSG.Quasithin.ChapterK.Linear.BinaryFiveSource
