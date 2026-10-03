module
public import ABG.ChapterII.Section1.WreathedExceptionalDefs

/-!
# Two small central extensions in the wreathed group

The exceptional-base subgroup consists of the ambient center and x₂. Adjoining
z gives the quaternion central product V; adjoining sz instead gives the other
central extension of the same order. These actual coordinate subgroups are used
in the proof of ABG Chapter II §1 Lemma 3 (article p.10): the second extension
has a two-group of automorphisms and is excluded by the theorem's hypothesis.
Their cardinalities, model identifications and automorphism properties are
proved separately; the definitions introduce no classification assumptions.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

/-- The common abelian base of the small central extensions. -/
@[expose] public def exceptionalBase : Subgroup S :=
  Subgroup.center S ⊔ Subgroup.zpowers P.x₂

/-- The central extension with outer generator sz. -/
@[expose] public def modularOvergroup : Subgroup S :=
  P.exceptionalBase ⊔ Subgroup.zpowers (P.s * P.z)

end ABG.Wreathed.Presentation
