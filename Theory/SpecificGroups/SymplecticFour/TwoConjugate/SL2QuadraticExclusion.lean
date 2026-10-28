module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SL2Quadratic
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.AbsolutelyIrreducible
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.QuadraticExclusion

/-!
# Excluding binary PSL₂ for the original moving opposite pair

The original moving-actor hypotheses make the literal opposite-pair action
absolutely irreducible. If this same group had a binary PSL₂ carrier, its
actual symplectic action would preserve a quadratic refinement. The source
central-root geometry excludes that form when the original subgroup has
more than two elements. This applies the degree-four module theorem to the
exact group and action of Aschbacher--Smith E.2.7, printed pp.219--220.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open Subgroup DiagramAutomorphisms EvenBorelTorus CentralRootGeometry
variable {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]

theorem not_psl2_of_moving_actor (hq : 2<Nat.card F)
    (a : ActorReduction.stabilizer (F:=F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom=V)
    (hc : V≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype)
    (hr : 2<Nat.card V) (f : ℕ) (hcard : Nat.card K=2^f) :
    ¬Nonempty (oppositePair V≃*Theory.PSL2.Group K) := by
  rintro ⟨e⟩
  obtain ⟨Q,hpolar,hQ⟩ := TransvectionRecognition.exists_quadratic_of_psl2_subgroup
    (oppositePair V) (pairAction_absolutelyIrreducible_of_moving_actor hq a ha V hV hc hr)
    e f hcard
  exact oppositePair_not_preserves_quadratic_of_moving_actor hq a ha V hV
    (parameter_range (F:=F) ▸ hc) hr Q hpolar (fun g hg => hQ ⟨g,hg⟩)
end Theory.SpecificGroups.SymplecticFour.TwoConjugate
