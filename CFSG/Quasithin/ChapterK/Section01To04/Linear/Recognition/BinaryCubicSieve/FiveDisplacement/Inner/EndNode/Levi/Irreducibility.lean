module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.GeometryData
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.ParabolicGeometry
public import Theory.Representation.BinaryUnipotentFixedSpace
public import Theory.Representation.Quotient

/-!
# Binary Smith–Timmesfeld irreducibility on the marked end-node fixed spaces

Timmesfeld's argument over the original binary field applies to the actual
upper and lower root groups. A unique opposite fixed line in the dual module
has a simple Levi span. The positive-unipotent orbit spans the dual, so
restriction of evaluation embeds the radical fixed space in the dual of
that simple Levi span. This proves irreducibility without a degree bound
or an algebraic-closure assumption.

The binary Curtis theorem and the concrete opposite-parabolic decompositions
discharge all the inputs of this argument. Both the literal relative two-core
quotient representation and its marked SL₄ action are therefore irreducible
for every finite-dimensional irreducible binary SL₅ representation. Faithfulness
is unnecessary; in particular the trivial irreducible module is included.

Source: GLS, Volume 3, Theorem 2.8.11 and preceding Theorem 2.8.9,
`refs/KGroup/GLS3/chapter2.tex`, pp.94–96; Guralnick–Malle,
Classification of 2F-modules II, Theorem 3.1 and Proposition 4.7(2).
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation
open Representation.BinaryUnipotentFixedSpace
namespace Levi
open Irreducibility
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- Evaluation does not change the action when the relative radical is
regarded as its ambient image. -/
def fixedSpaceLeviEquiv (e : Fin 2) :
    (fixedSubrepresentation σ (radicalImage e) (leviSubgroup e)
      (levi_normalizes_radicalImage e)).toRepresentation.Equiv
      ((quotientRepresentation σ e).comp (leviToQuotient e)) :=
  .mk (LinearEquiv.ofEq _ _ (invariants_radicalImage σ e)) (by
    intro l
    ext v
    rfl)

/-- Conditional Smith–Timmesfeld application to the literal quotient and
its original-coordinate SL₄ marking. -/
theorem action_irreducible_of_unipotent_inputs [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (e : Fin 2) (hc : CurtisInput σ.dual)
    (hRU : radicalImage e ≤ upper)
    (hUL : upper ≤ radicalImage e ⊔ leviSubgroup e)
    (hTL : lower ≤ oppositeRadical e ⊔ leviSubgroup e)
    (hq : Function.Surjective (leviToQuotient e)) :
    IsIrreducible (action σ e) := by
  obtain ⟨z, hz0, hz, hline, hspan⟩ := hc
  have hi := fixedSubrepresentation_irreducible σ (radicalImage e) (leviSubgroup e)
    (oppositeRadical e) upper lower (radicalImage_isPGroup e) lower_isPGroup
    (levi_normalizes_radicalImage e) (levi_normalizes_oppositeRadical e)
    (Subgroup.map_mono hRU) hTL hUL z hz0 hz hline hspan
  have hiL : IsIrreducible ((quotientRepresentation σ e).comp (leviToQuotient e)) :=
    (RepEquiv.ofRepresentationEquiv (fixedSpaceLeviEquiv σ e)).symm.irreducible_of_euqiv hi
  have hiQ : IsIrreducible (quotientRepresentation σ e) :=
    (irreducible_comp_surjective_iff (leviToQuotient e) hq _).mp hiL
  exact (irreducible_comp_surjective_iff (quotientEquiv e).symm.toMonoidHom
    (quotientEquiv e).symm.surjective _).mpr hiQ

/-- Binary Smith–Timmesfeld: the end-parabolic radical fixed space is
irreducible for its marked SL₄ quotient, without a faithfulness assumption. -/
theorem action_irreducible [FiniteDimensional (ZMod 2) V] [IsIrreducible σ]
    (e : Fin 2) : IsIrreducible (action σ e) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  let : IsIrreducible σ.dual := isIrreducible_dual
  exact action_irreducible_of_unipotent_inputs σ e (curtisInput σ.dual)
    (radicalImage_le_upper e) (upper_le_radicalImage_sup_leviSubgroup e)
    (lower_le_oppositeRadical_sup_leviSubgroup e) (leviToQuotient_surjective e)

end Levi

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- The literal quotient of the end-parabolic by its relative two-core acts
irreducibly on the radical fixed space of an irreducible binary SL₅ module. -/
theorem quotientRepresentation_irreducible [FiniteDimensional (ZMod 2) V]
    [IsIrreducible σ] (e : Fin 2) : IsIrreducible (quotientRepresentation σ e) :=
  (irreducible_comp_surjective_iff (Levi.quotientEquiv e).symm.toMonoidHom
    (Levi.quotientEquiv e).symm.surjective _).mp (Levi.action_irreducible σ e)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
