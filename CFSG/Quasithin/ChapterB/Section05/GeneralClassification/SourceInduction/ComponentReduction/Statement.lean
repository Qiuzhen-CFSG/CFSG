module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection

/-!
# Literal targets for the B.5.9–10 component reduction

The five alternatives refer to W=[V,L] and its actual central quotient.
Natural actions retain a group isomorphism and one compatible intertwiner;
the doubled case uses the same actor on both copies. The two distinct
four-dimensional extensions in B.4.8 are kept separate.

The intermediate natural seed has only the LA-action justified at that point
of the proof. Its equality with W is a remaining theorem, never an input here.
The final records specify conclusions, not hypotheses or a proof of B.5.9–10.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.4.8(2), p.91,
and B.5.9–10, printed pp.107–109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Conjugation by each member of A agrees on L with conjugation by a member of L. -/
def InducesInner (A L : Subgroup G) : Prop :=
  ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹

/-- B.4.8(2), on the four-dimensional module whose central quotient is natural.
This is different from `FourDimensionalSource`, which encodes B.4.8(3). -/
structure FourDimensionalCoverSource where
  dimension : Module.finrank (ZMod 2) V = 4
  indecomposable : IsIndecomposable ρ
  natural : ActionEquiv (reducedAction ρ) (linearNatural BinaryField.two 3)
  offenders : ∀ A, IsBestOffender ρ A ↔
    IsFullCenterGroup BinaryField.two 3 (A.map natural.groupEquiv.toMonoidHom)
  ratio : quadraticRatio ρ = 1
  sylow_fixed : ∀ T : Sylow 2 G, fixedSpace ρ (T : Subgroup G) = ρ.invariants
  involutions : ∀ a : G, orderOf a = 2 →
    moved ρ (zpowers a) = fixedSpace ρ (zpowers a) ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2

/-- The five B.5.9 conclusions, indexed by the actual first factor of B.5.10.
All module assertions concern W=[V,L] or its specified central quotient. -/
inductive ComponentActionCase (A L : Subgroup G) (s : MovedSection ρ L) :
    Subgroup G → Prop
  | linearTwo (F : BinaryField)
      (natural : IsLinearNatural (s.action.comp L.subtype) F 2)
      (sylow : ∃ T : Sylow 2 L, A = (T : Subgroup L).map L.subtype)
      (supplement : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
      ComponentActionCase A L s L
  | symmetricFive
      (action : MarkedActionEquiv s.space.toRepresentation (L ⊔ A) L
        (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
      (order : Nat.card A = 2)
      (supplement : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
      ComponentActionCase A L s (L ⊔ A)
  | doubleThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2)
      (contained : A ≤ L)
      (supplement : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
      ComponentActionCase A L s L
  | naturalThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsLinearNatural (s.space.toRepresentation.comp L.subtype) F 3)
      (inner : InducesInner A L) :
      ComponentActionCase A L s L
  | fourCover
      (cover : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype))
      (klein : Nonempty (A ≃* Multiplicative (Fin 2 → ZMod 2)))
      (contained : A ≤ L)
      (supplement : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
      ComponentActionCase A L s L

/-- The two-core is taken inside LA and then mapped into the original group. -/
def localTwoCore (L A : Subgroup G) : Subgroup G :=
  (pCore 2 ↥(L ⊔ A)).map (L ⊔ A).subtype

/-- The literal U=[C_V(O₂(LA)),L] in the proof of B.5.9. -/
noncomputable def naturalSeedSpace (L A : Subgroup G) : Submodule (ZMod 2) V :=
  subspaceCommutator ρ (fixedSpace ρ (localTwoCore L A)) L

/-- Case (IV) before proving that U=W. The action on U is only an LA-action;
ambient G-invariance is not assumed before this equality is proved. -/
structure NaturalSeed (A L : Subgroup G) where
  field : BinaryField
  odd_degree : Odd field.degree
  space : Subrepresentation (ρ.comp (L ⊔ A).subtype)
  space_eq : space.toSubmodule = naturalSeedSpace ρ L A
  natural : ActionEquiv (space.toRepresentation.comp
    (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left))) (linearNatural field 3)
  inner : InducesInner A L

/-- A proof boundary before the last paragraph of B.5.9. This is an output
specification, not an earlier-source assumption. -/
inductive PreliminaryConclusion (A L : Subgroup G) (s : MovedSection ρ L) : Prop
  | classified (H : Subgroup G) (case : ComponentActionCase ρ A L s H)
  | naturalSeed (seed : NaturalSeed ρ A L)

/-- The exact exceptional configuration used in B.5.10. -/
def IsExceptional (H : Subgroup G) (W : Subrepresentation ρ) : Prop :=
  IsLinearNatural (W.toRepresentation.comp H.subtype) BinaryField.two 3 ∧
    Module.finrank (ZMod 2) (V ⧸ (W.toSubmodule ⊔ fixedSpace ρ H)) = 1

/-- B.5.10, with G₂ literally the centralizer of the chosen G₁. The fields
are conclusions to establish from B.5.9 and earlier source results. -/
structure ProductConfiguration (H : Subgroup G) (W : Subrepresentation ρ) where
  first_normal : H.Normal
  second_normal : (centralizer (H : Set G)).Normal
  fixed : Subrepresentation ρ
  fixed_eq : fixed.toSubmodule = fixedSpace ρ H
  product : InternalProduct H (centralizer (H : Set G))
  centralizer_eq : centralizer (H : Set G) = subspaceKernel ρ W.toSubmodule ⊤
  configuration : W.toSubmodule ⊔ fixed.toSubmodule = ⊤ ∨ IsExceptional ρ H W

/-- The full component-reduction target, retaining the chosen minimal offender,
component and all five group/module alternatives. This definition proves none
of its fields. -/
structure Conclusion where
  offender : Subgroup G
  minimal : IsMinimalBestOffender ρ offender
  component : Subgroup G
  isComponent : IsComponent G component
  component_normal : component.Normal
  commutator_eq : ⁅component, offender⁆ = component
  sectionData : MovedSection ρ component
  first : Subgroup G
  actionCase : ComponentActionCase ρ offender component sectionData first
  productConfiguration : ProductConfiguration ρ first sectionData.space

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
