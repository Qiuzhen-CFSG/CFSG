module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Statement
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Actions
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The one-copy classification row in the full original normalizer action

On a binary three-space every invertible linear map is in SL₃(2). Thus
the actual normalizer action transports through the component's natural
coordinates to an SL₃(2) quotient. Component equivariance proves that its
restriction to L is onto. This constructs the NaturalMarking required by
the orbit theorem from the literal one-copy classification data.

Source: Aschbacher--Smith 13.1.10(3) and 13.1.12, pp.871--873.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}
variable [IsElementaryAbelian 2 (normalizerMoved L)]

omit [Finite G] in
/-- Full normalizer transport on the same original U. -/
def naturalOrbitMarking
    (a : ActionEquiv (componentRepresentation (L := L))
      (linearNatural BinaryField.two 3)) : LinearThree.NaturalMarking L := by
  let e := a.linearEquiv
  let ρ := Representation.elementaryRepresentation (p := 2) (action L)
  let ν : Representation (ZMod 2) (normalizer (L : Set G)) BinaryLinearThree.Vector :=
    e.conjRingEquiv.toMonoidHom.comp ρ
  let q : normalizer (L : Set G) →* BinaryLinearThree.Group :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        BinaryLinearThree.Vector).toMonoidHom.comp ν.asGroupHom)
  have he (m : normalizer (L : Set G)) (v : normalizerMoved L) :
      e (Additive.ofMul (action L m v)) = BinaryLinearThree.W (q m) (e (Additive.ofMul v)) := by
    change _ = BinaryLinear.OuterCyclic.slEquivLinear 3
      ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm _) _
    rw [MulEquiv.apply_symm_apply]
    change e _ = e (ρ m (e.symm (e (Additive.ofMul v))))
    rw [e.symm_apply_apply]
    rfl
  refine ⟨q,?_,e.toAddEquiv.toMultiplicative,he⟩
  intro g
  let g' : Matrix.SpecialLinearGroup (Fin 3) BinaryField.two.Carrier := g
  obtain ⟨l,hl⟩ := (componentAction L).rangeRestrict_surjective (a.groupEquiv.symm g')
  refine ⟨l,?_⟩
  apply Representation.specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := e.surjective v
  have hh := a.intertwines ((componentAction L).rangeRestrict l) w
  have hg : a.groupEquiv ((componentAction L).rangeRestrict l) = g' :=
    (congrArg a.groupEquiv hl).trans (a.groupEquiv.apply_symm_apply g')
  rw [hg] at hh
  exact (he (inclusion L.le_normalizer l) w.toMul).symm.trans hh

omit [Finite G] in
/-- Collapse the single repeated copy without changing either action. -/
def oneCopyNaturalAction
    (a : ActionEquiv (componentRepresentation (L := L))
      (repeated (linearNatural BinaryField.two 3) 1)) :
    ActionEquiv (componentRepresentation (L := L)) (linearNatural BinaryField.two 3) := by
  let e : (Fin 1 → BinaryLinearThree.Vector) ≃ₗ[ZMod 2] BinaryLinearThree.Vector :=
    { toFun := fun v => v 0
      invFun := fun v _ => v
      left_inv := fun v => funext fun i => congrArg v (Subsingleton.elim _ _)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨a.groupEquiv,a.linearEquiv.trans e,?_⟩
  intro g v
  exact congrArg (fun w => w 0) (a.intertwines g v)

/-- The actual one-copy classification data discharge both consumer inputs. -/
theorem centralizer_inputs_of_one_copy {p : ℕ} [Fact p.Prime]
    (h : Context T L p)
    (ha : IsRepeatedLinearNatural (componentRepresentation (L := L)) BinaryField.two 3 1) :
    OrbitFacts T L p ∧ SieveActions h := by
  obtain ⟨a⟩ := ha
  let d := naturalOrbitMarking (oneCopyNaturalAction a)
  exact ⟨d.orbitFacts h,d.sieveActions h⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
