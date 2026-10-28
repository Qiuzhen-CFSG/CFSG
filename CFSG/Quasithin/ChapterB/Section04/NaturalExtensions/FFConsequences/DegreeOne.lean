module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryThree
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.SmallFields

/-!
# Carrier-independent binary SL₃ FF extensions

The prime-field action equivalence transports only the marked natural
coordinates. The original representation, submodule and quotient map stay
literal, so the binary splitting theorem applies to any field of degree one.
This is the field-carrier adapter for B.4.9(2)(i)–(ii), Aschbacher–Smith,
combined manuscript of 1 March 2004, printed pp.92–94.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource
namespace DoubleNatural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  {F : BinaryField} (d : DoubleNatural F 3 ρ)

/-- The degree-one conclusion is independent of which carrier presents F₂. -/
theorem degree_one_three_ff (hF : F.degree = 1) (hff : IsFFModule ρ) : d.Splits ∧
    Nonempty (d.space.quotientRepresentation.Equiv d.space.toRepresentation) ∧
      quadraticRatio ρ = 1 := by
  let eTop : ActionEquiv (d.space.toRepresentation.comp (⊤ : Subgroup G).subtype)
      (linearNatural F 3) :=
    ⟨Subgroup.topEquiv.trans d.natural.groupEquiv, d.natural.linearEquiv,
      fun g v => d.natural.intertwines g v⟩
  let e := ChapterK.Linear.Natural.primeFieldActionEquiv d.space.toRepresentation ⊤ F hF 3 eTop
  let d' : DoubleNatural BinaryField.two 3 ρ :=
    { faithful := d.faithful
      space := d.space
      natural :=
        ⟨Subgroup.topEquiv.symm.trans e.groupEquiv, e.linearEquiv,
          fun g v => e.intertwines ⟨g, Subgroup.mem_top g⟩ v⟩
      quotient := d.quotient }
  exact d'.binary_three_ff hff
end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
