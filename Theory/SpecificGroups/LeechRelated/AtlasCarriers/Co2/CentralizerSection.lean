module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection.Action

/-!
# A symplectic quotient of an actual Co₂ involution centralizer

The first fixed ATLAS generator is an involution. Two explicit centralizing
words generate a subgroup whose action on 63 colored blocks is the full
six-dimensional binary symplectic group. Composing that action with the
central projection constructs the projective symplectic quotient. Its kernel
is normal inside the numerator; no splitting or ambient normality is used.

This supplies the section required by Aschbacher–Smith A.2.19, printed
pp. 40–41, for the Co₂ row of GLS3 Table 5.3k. The construction proves neither
full centralizer equality nor a global order or simplicity assertion.
-/

public section
namespace Sporadic.LeechRelated.Co2.CentralizerSection

/-- The actual projective quotient of the centralizing word subgroup. -/
noncomputable def quotientMap : numerator →*
    (Matrix.symplecticGroup (Fin 3) (ZMod 2) ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 3) (ZMod 2))) :=
  (QuotientGroup.mk' _).comp symplecticMap

/-- Every projective symplectic matrix is realized by a centralizing word. -/
theorem quotientMap_surjective : Function.Surjective quotientMap :=
  (QuotientGroup.mk'_surjective _).comp symplecticMap_surjective

end Sporadic.LeechRelated.Co2.CentralizerSection
