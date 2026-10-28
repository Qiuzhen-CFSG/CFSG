module

public import Theory.Representation.SL2NaturalOffenders.Internal
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.SL2NaturalOffenders.FieldAction

/-!
# Offenders in extensions of the natural SL₂ action

Let a finite group act faithfully on the natural binary module of a specified
normal SL₂ subgroup, over a finite field of order greater than two. Every
offender is the image of a Sylow two-subgroup of this normal layer.

Normality forces the ambient actors to be semilinear. The field-action estimate
then makes every offender linear over the matrix field. Its elements have
determinant one, so faithfulness places the offender in the specified SL₂
layer. Counting fixed vectors forces it to fill a Sylow two-subgroup.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the offender conclusion in the natural-module case
B.4.2(1), printed p.86, as used in C.2.7, printed pp.145–146. This intrinsic
model theorem does not use the full offender classification.
-/

public section

namespace Representation.SL2NaturalOffenders
open Representation.BinaryOffender
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group H] [Finite H]

/-- Every offender acting linearly over the field of the specified natural
SL₂ layer is the image of a Sylow two-subgroup of that layer. -/
theorem exists_sylow_of_linear (L : Subgroup H)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {A : Subgroup H} (hA : IsOffender ρ A)
    (hlinear : ∀ a ∈ A, ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = c • ρ a v) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = A := by
  let : IsElementaryAbelian 2 A := hA.1.2
  apply exists_sylow_of_le L e ρ hnat hA
  intro a ha
  exact mem_of_linear_square_one L e ρ hfaith hnat
    (elemPow_eq_one_of_isElementaryAbelian a ha) (hlinear a ha)

/-- Every binary offender in a faithful extension of the natural action of a
normal SL₂ subgroup is the image of a Sylow two-subgroup of that subgroup. -/
theorem exists_sylow (hF : 2 < Nat.card F) (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {A : Subgroup H} (hA : IsOffender ρ A) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = A := by
  exact exists_sylow_of_linear L e ρ hfaith hnat hA
    (offender_fieldLinear hF ρ hfaith (normalizer_semilinear L e ρ hnat) hA)

end Representation.SL2NaturalOffenders
