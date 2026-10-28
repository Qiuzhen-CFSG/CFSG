module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Alternating
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Tits.FiniteImageOrder
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Two small characteristic-two endpoints

The actual derived projective symplectic carrier is isomorphic to A₆ via
the faithful six-letter polar representation. The alternating exclusion
therefore applies. Parrott's actual Tits carrier surjects onto its certified
finite image of order prime to seven. The supplied simplicity makes this
map injective; the specified component supplies a subgroup of order 168.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137, and Theorem C
with Remark A.2.4, p.33. Only the finite quotient of Parrott's presentation
is needed; no independent simplicity or presentation-order proof is used.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
universe u
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- At field order two the fixed component would fill the ambient PSL₃. -/
theorem SimpleInput.not_binary_linear_three [Finite S] :
    ¬ ClassicalGroup.IsPSL S 3 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact EvenModels.card_ne_component s
    ((Nat.card_congr (e.trans (Atlas.fieldEquivPSL 3 eF)).toEquiv).trans
      Matrix.PSL3Two.card_PSL)

/-- The actual Sp₄(2)′ constructor is excluded through its proved A₆ equivalence. -/
theorem SimpleInput.not_symplectic_derived :
    ¬ Nonempty (S ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rintro ⟨e⟩
  exact s.not_alternating (by decide : 6 ≤ 8)
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

/-- The nontrivial finite quotient of the actual Tits carrier, together with
the given simplicity, excludes its occurrence. -/
theorem SimpleInput.not_tits : ¬ Nonempty (S ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  let : IsSimpleGroup S := s.simple
  let : Nontrivial Tits.Atlas1600Group := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [Tits.atlas1600Group_card]; norm_num)
  let f := Tits.parrottFiniteImageMap.comp e.toMonoidHom
  have hf : Function.Injective f := f.injective_of_surjective_of_simple
    (Tits.parrottFiniteImageMap_surjective.comp e.surjective)
  have h := (EvenModels.seven_dvd_card s).trans (Subgroup.card_dvd_of_injective f hf)
  rw [Tits.atlas1600Group_card] at h
  norm_num at h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
