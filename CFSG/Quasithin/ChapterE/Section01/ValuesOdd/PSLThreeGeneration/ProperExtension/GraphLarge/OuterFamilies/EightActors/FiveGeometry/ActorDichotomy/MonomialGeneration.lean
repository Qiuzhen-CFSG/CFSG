module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.Families
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.NormalizerCertificate.Assembly

/-!
# The first PSL₃(5) actor orbit

The explicit weak-closure and matrix certificate in
`NormalizerCertificate.Assembly` proves the concrete `MonomialJoin` statement
for the literal graph extension of `PSL₃(5)`.  This module publishes that
calculation at the `ActorDichotomy` boundary and applies it to the solvable
join and the arbitrary-family consumer.  The reselection premise for the
other actor orbit remains an explicit input to the latter application.

Source: Aschbacher--Smith E.1.1--5 and E.1.14(7), printed pp.209--214.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
open FiveSourceAudit PSUThreeGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The full monomial-normalizer generation calculation for the first actor
orbit in the literal `PSL₃(5):2` model. -/
theorem monomialJoin : MonomialJoin :=
  NormalizerCertificate.monomialJoin

/-- The monomial calculation supplies a solvable generating overgroup at each
Sylow; this is the direct consumer of `solvable_join_at_every_sylow`. -/
theorem solvable_join_of_monomialJoin (T : Sylow 2 Model) :
    ∃ H : Subgroup Model, (T : Subgroup Model) ≤ H ∧ Group.IsSolvable H ∧
      H ⊔ normalizer (weakClosure (T : Subgroup Model) family : Set Model) = ⊤ :=
  solvable_join_at_every_sylow monomialJoin T

/-- The complete first-orbit consumer retains the independent reselection
premise for actors outside the original conjugacy family. -/
theorem fiveGeometry_model_of_monomialJoin
    (T : Sylow 2 Model) (Ω : Set (Subgroup Model)) (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup Model) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup Model) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup Model))
    (hcard : Nat.card A = 8) (z : Model) (hreselect : ReselectionAt T z)
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    FiveGeometryAt (ZMod 5) T Ω z :=
  fiveGeometry_model_of_calculations monomialJoin T Ω hΩ hEight A hA hAT hcard z
    hreselect hmodel

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
