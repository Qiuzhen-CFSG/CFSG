module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.SmallFields
public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification
public import Theory.Representation.BinaryNaturalDual.FiveActors.Hyperplanes
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source

/-!
# The marked binary coordinates for B.4.9 in dimension five

Prime-field transport changes the carrier of the defining field while keeping
the original submodule and quotient. Composing the resulting special-linear
marking with the actual SL-to-GL equivalence identifies the actor with GL₅(2).
The intertwining identity below retains the module marking, as needed for
both radical placement and the fixed-space calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9,
printed pp.94–95.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)

/-- The original natural submodule with prime-field matrix coordinates. -/
noncomputable def coordinates : ActionEquiv d.space.toRepresentation
    (linearNatural BinaryField.two 5) := by
  let eTop : ActionEquiv (d.space.toRepresentation.comp (⊤ : Subgroup G).subtype)
      (linearNatural F 5) :=
    ⟨Subgroup.topEquiv.trans d.natural.groupEquiv, d.natural.linearEquiv,
      fun g v => d.natural.intertwines g v⟩
  let e := ChapterK.Linear.Natural.primeFieldActionEquiv
    d.space.toRepresentation ⊤ F hF 5 eTop
  exact ⟨Subgroup.topEquiv.symm.trans e.groupEquiv, e.linearEquiv,
    fun g v => e.intertwines ⟨g, Subgroup.mem_top g⟩ v⟩

/-- The genuine actor isomorphism, coherent with `coordinates.linearEquiv`. -/
noncomputable def groupEquiv : G ≃* LinearGroup 5 :=
  (coordinates d hF).groupEquiv.trans (slEquivLinear 5)

theorem intertwines (g : G) (v : d.space.toSubmodule) :
    (coordinates d hF).linearEquiv (d.space.toRepresentation g v) =
      groupEquiv d hF g ((coordinates d hF).linearEquiv v) := by
  exact (coordinates d hF).intertwines g v

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
