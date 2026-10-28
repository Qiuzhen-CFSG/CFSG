module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF

/-!
# The SL₃ source branch of B.4.2

The original quasisimple component, faithful irreducible binary action and
member of P(G,V) now determine the natural SL₃ action. The completed natural
calculation gives the sharp ratio, containment of every best offender,
generation of the component and the corrected B.4.2 action row. The field
parameter is retained from the actual projective quotient.

Source: Aschbacher–Smith, B.4.2(2) and K.3.2, printed pp.86 and 454–456.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Linear.SourceFF
open ChapterB.QuasisimpleSource Recognition.SourceFF

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}

/-- The original PSL₃ family hypotheses construct its natural model and all
of its source offender conclusions. The exponent is the given quotient
parameter, not an independently chosen representation parameter. -/
theorem source_of_bestOffender
    (hsqtk : IsSQTK K G) (hfit : L = generalizedFitting G)
    (hquasi : IsQuasisimple L) (hfaith : Function.Injective ρ)
    (hirr : IsIrreducible (ρ.comp L.subtype))
    (r : ℕ) (hr : 0 < r)
    (hquot : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ r))
    (A : Subgroup G) (hA : IsBestOffender ρ A) :
    ∃ B : BinaryField, B.degree = r ∧
      Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural B 3)) ∧
      quadraticRatio ρ = 1 / 2 ∧
      (∀ D, IsBestOffender ρ D → D ≤ L) ∧ offenderSubgroup ρ = L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
        ρ L (offenderSubgroup ρ) := by
  have hff : IsFFModule ρ := ⟨A, hA.isOffender ρ⟩
  have hc : cubicRatio ρ ≤ 2 :=
    ((isFFModule_iff_cubicRatio_le_one ρ).mp hff).trans (by norm_num)
  let h : Recognition.SourceHypothesis K ρ L :=
    ⟨inferInstance, inferInstance, hsqtk, hfit.symm, hquasi, hfaith, hirr, hc⟩
  obtain ⟨B, hB, eQ, C, _⟩ := exists_binaryField_cover h r hr hquot
  obtain ⟨hn⟩ := naturalSourceInput_of_ff h C eQ hff
  obtain ⟨hq, ha, hg, hrow⟩ := Natural.source_natural ρ L B 3 hn
  exact ⟨B, hB, ⟨hn.natural⟩, by simpa using hq, ha, hg, hrow⟩

/-- Direct application in the B.4 dispatcher to its literal family
alternative and best offender, with every recognition premise discharged. -/
theorem actionCase_of_bestOffender
    (hsqtk : IsSQTK K G) (hfit : L = generalizedFitting G)
    (hquasi : IsQuasisimple L) (hfaith : Function.Injective ρ)
    (hirr : IsIrreducible (ρ.comp L.subtype))
    (r : ℕ) (hr : 0 < r)
    (hquot : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ r))
    (A : Subgroup G) (hA : IsBestOffender ρ A) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      ρ L (offenderSubgroup ρ) := by
  obtain ⟨_, _, _, _, _, _, hrow⟩ :=
    source_of_bestOffender ρ hsqtk hfit hquasi hfaith hirr r hr hquot A hA
  exact hrow

end CFSG.Quasithin.ChapterK.Linear.SourceFF
