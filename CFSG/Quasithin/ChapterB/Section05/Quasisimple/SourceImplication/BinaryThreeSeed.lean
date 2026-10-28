module
public import Theory.Representation.BinaryLinear.ThreeCubicFixedSpace
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.CubicMoved
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.Representation.NormalElementaryFixedSeed
/-!
# Binary SL₃ source modules conflict with the actual Sylow seed

The canonical binary field marking preserves the natural matrix action and
all repeated copies. The explicit point-radical cubic witness then lifts
through the original moved quotient, or directly from its moved space.
The resulting element outside the prescribed Sylow fixes the seed, which
contradicts the seed's exact centralizer. All original conjugation maps and
both B.5 module markings are retained.
Source: Aschbacher–Smith B.5.1(1)(i–ii) and15.4.20, printed pp.99 and1164.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
open BinaryLinear
noncomputable def binaryThreeNaturalCoordinates :
    ActionEquiv (linearNatural BinaryField.two 3) ThreeFixedSpace.natural := by
  refine ⟨OuterCyclic.slEquivLinear 3,LinearEquiv.refl _ _,?_⟩
  intro g v
  exact (OuterCyclic.slEquivLinear_apply 3 g v).symm

noncomputable def binaryThreeRepeatedCoordinates (r : ℕ) :
    ActionEquiv (repeated (linearNatural BinaryField.two 3) r) (ThreeFixedSpace.copies r) := by
  refine ⟨OuterCyclic.slEquivLinear 3,LinearEquiv.refl _ _,?_⟩
  intro g v
  funext i
  exact binaryThreeNaturalCoordinates.intertwines g (v i)

private noncomputable def compose
    {A B C X Y Z : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) A X} {σ : Representation (ZMod 2) B Y}
    {τ : Representation (ZMod 2) C Z} (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) :
    ActionEquiv ρ τ :=
  ⟨e.groupEquiv.trans f.groupEquiv,e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans
      (f.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (V Z : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))

/-- The exact single-natural B.5 row has no Sylow-centralizer seed. -/
theorem not_binaryThree_movedSection_of_seed
    (hZV : Z ≤ V) (P : Sylow 2 G) (hCZ : centralizer (Z : Set G) = (P : Subgroup G))
    (J C : Subgroup Q)
    (s : MovedSection ((NormalElementaryQuotient.representation V q hq hk).comp J.subtype)
      (C.subgroupOf J)) (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (linearNatural F 3)) : False := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let e' := compose (compose e (ExtensionConsequences.degreeOneNaturalEquiv F hF 3))
    binaryThreeNaturalCoordinates
  obtain ⟨g,hg,_,hfix⟩ := MovedSection.cubic_enlargement ρ J C s ThreeFixedSpace.natural e'
    ThreeFixedSpace.unipotent ThreeFixedSpace.unipotent_two ThreeFixedSpace.cycle
    ThreeFixedSpace.cycle_pow ThreeFixedSpace.cycle_ne_one ThreeFixedSpace.cycle_normalizes
    ThreeFixedSpace.cycle_fixes_natural (P.mapSurjective hq)
  exact NormalElementaryQuotient.no_fixedSpace_enlargement_of_seed
    V Z q hq hk hZV (P : Subgroup G) hCZ g hg hfix

/-- The exact repeated-natural B.5 moved space has the same obstruction. -/
theorem not_binaryThree_movedSpace_of_seed
    (hZV : Z ≤ V) (P : Sylow 2 G) (hCZ : centralizer (Z : Set G) = (P : Subgroup G))
    (J C : Subgroup Q)
    (s : MovedSection ((NormalElementaryQuotient.representation V q hq hk).comp J.subtype)
      (C.subgroupOf J)) (F : BinaryField) (hF : F.degree = 1) (r : ℕ)
    (e : ActionEquiv (s.space.toRepresentation.comp (C.subgroupOf J).subtype)
      (repeated (linearNatural F 3) r)) : False := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let e' := compose (compose e (ExtensionConsequences.degreeOneRepeatedEquiv F hF 3 r))
    (binaryThreeRepeatedCoordinates r)
  obtain ⟨g,hg,_,hfix⟩ := MovedSection.space_cubic_enlargement ρ J C s (ThreeFixedSpace.copies r) e'
    ThreeFixedSpace.unipotent ThreeFixedSpace.unipotent_two ThreeFixedSpace.cycle
    ThreeFixedSpace.cycle_pow ThreeFixedSpace.cycle_ne_one ThreeFixedSpace.cycle_normalizes
    (ThreeFixedSpace.cycle_fixes_copies r) (P.mapSurjective hq)
  exact NormalElementaryQuotient.no_fixedSpace_enlargement_of_seed
    V Z q hq hk hZV (P : Subgroup G) hCZ g hg hfix

end CFSG.Quasithin.ChapterB.QuasisimpleSource
