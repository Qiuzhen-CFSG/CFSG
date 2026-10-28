module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FourSpace
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The original rank-one quotient supplies the moving-seed comparison

The kernel of the component action is a proper normal subgroup of an
intrinsic C-component, hence solvable. The literal L1 action kernel embeds
in it. Since L1 is perfect with simple PSL2(4) two-core quotient, the same
quotient survives in its image. Consequently five divides the order of the
marked seed image, supplying the premise of the four-dimensional exclusion.

The chosen-flag application retains only the earlier rank-one quotient
marking and the previously authorized source geometry. No order bound or
representation exclusion is supplied by the caller. The six-space recognition
and field-witness construction remain separate source obligations.
Source: Aschbacher--Smith, 11.4.2, printed p.777, with the original flag
quotients of section 11.1 and A.3.3(1).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Restrict the literal component-action projection to the original L1. -/
def seedProjection : E.L₁ →* seedImage E :=
  ((projection E).subgroupMap (E.L₁.subgroupOf (localGroup E))).comp
    (subgroupOfEquivOfLe ((le_conjugateSpanBy _ _).trans le_sup_left)).symm.toMonoidHom

/-- The marked seed image is exactly the image of this projection. -/
theorem seedProjection_surjective : Function.Surjective (seedProjection E) :=
  ((projection E).subgroupMap_surjective _).comp (subgroupOfEquivOfLe _).symm.surjective

/-- Properness of the component-action kernel gives a solvable seed kernel. -/
theorem seedProjection_ker_solvable
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E) : Group.IsSolvable (seedProjection E).ker := by
  let f := (projection E).subgroupMap (component E)
  obtain ⟨e⟩ := hmodel.2
  let : Nontrivial (componentImage E) := e.toEquiv.nontrivial
  have hproper : f.ker ≠ ⊤ := by
    intro ht
    obtain ⟨x,hx⟩ := exists_ne (1 : componentImage E)
    obtain ⟨k,rfl⟩ := (projection E).subgroupMap_surjective (component E) x
    exact hx (show k ∈ f.ker from ht.symm ▸ mem_top k)
  let : Group.IsSolvable f.ker := hstar.1.1.isSolvable_of_subnormal_lt_top
    (inferInstance : f.ker.Normal).isSubnormal hproper
  let j : (seedProjection E).ker →* f.ker := {
    toFun := fun x => ⟨⟨⟨x.val.val,
      ((le_conjugateSpanBy _ _).trans le_sup_left) x.val.property⟩,
      (le_conjugateSpanBy _ _) x.val.property⟩, ?_⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  · exact Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun k : f.ker => (((k : component E) : localGroup E) : G)) hxy)))
  · apply Subtype.ext
    have hx : seedProjection E x.val = 1 := x.property
    exact congrArg (fun k : seedImage E => (k : ActionQuotient E)) hx

/-- The earlier PSL2(4) quotient survives modulo the image two-core. -/
theorem five_dvd_seedImage
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    5 ∣ Nat.card (seedImage E) := by
  have hF : Nat.card E.input.field.Carrier = 4 := by
    rw [E.input.field.card_eq, hmodel.1]
    rfl
  obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) :=
    (e.trans d).isSimpleGroup
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsSolvable (seedProjection E).ker := seedProjection_ker_solvable E hstar hmodel
  let t := PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    (seedProjection E) (seedProjection_surjective E)
  have hc : Nat.card (seedImage E ⧸ pCore 2 (seedImage E)) = 60 := by
    rw [Nat.card_congr (t.symm.trans (e.trans d)).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hdvd : Nat.card (seedImage E ⧸ pCore 2 (seedImage E)) ∣ Nat.card (seedImage E) :=
    card_dvd_of_surjective _ (QuotientGroup.mk'_surjective _)
  exact dvd_trans (hc.symm ▸ (by decide : 5 ∣ 60)) hdvd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The source four-space exclusion with the order premise discharged. -/
theorem no_four_section_of_seed_quotient (E : Closure.Geometry D)
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (s : MovedSection (action E) (componentImage E))
    (hi : ExtensionConsequences.IrreducibleAlternative (componentImage E) s) :
    Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≠ 4 :=
  no_four_section E h hf hne hstar hcent hmodel (five_dvd_seedImage E hstar hmodel e) s hi

/-- Application to the original flag and literal rank-one quotient marking. -/
theorem ofFlag_no_four_section_of_seed_quotient
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (s : MovedSection (action (ofFlag S f X z H)) (componentImage (ofFlag S f X z H)))
    (hi : ExtensionConsequences.IrreducibleAlternative (componentImage (ofFlag S f X z H)) s) :
    Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≠ 4 :=
  no_four_section_of_seed_quotient _ h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent hmodel e s hi

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
