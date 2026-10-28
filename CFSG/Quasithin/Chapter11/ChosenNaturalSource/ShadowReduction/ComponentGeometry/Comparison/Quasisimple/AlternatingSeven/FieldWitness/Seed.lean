module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Actor
public import Theory.SpecificGroups.Alternating.SevenFiveSection
/-!
# The original seed image is PSL2(4)

The solvable kernel preserves the two-core quotient of the perfect seed.
Inside the actual A7 component, an A5 section has trivial two-core. Removing
this core identifies the marked seed image with the original field model.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

theorem seedImage_twoCore_eq_bot
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    pCore 2 (seedImage E) = ⊥ := by
  have hF : Nat.card E.input.field.Carrier = 4 := by rw [E.input.field.card_eq,hmodel.1]; rfl
  let d := Classical.choice (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF)
  obtain ⟨c⟩ := hmodel.2
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := (e.trans d).isSimpleGroup
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsSolvable (seedProjection E).ker := seedProjection_ker_solvable E hstar hmodel
  let r := PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    (seedProjection E) (seedProjection_surjective E)
  let j := c.toMonoidHom.comp (inclusion (seedImage_le_componentImage E))
  have hj : Function.Injective j := c.injective.comp (inclusion_injective _)
  let b := MonoidHom.ofInjective hj
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hbot := alternatingGroup.SevenFiveSection.twoCore_eq_bot j.range
    (bq.symm.trans (r.symm.trans (e.trans d)))
  have hh := pCore_map_iso 2 b
  rw [hbot] at hh
  exact (map_eq_bot_iff_of_injective _ b.injective).mp hh

@[expose] def seedImageEquiv
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    seedImage E ≃* PSL(2,E.input.field.Carrier) := by
  have hF : Nat.card E.input.field.Carrier = 4 := by rw [E.input.field.card_eq,hmodel.1]; rfl
  let d := Classical.choice (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF)
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := (e.trans d).isSimpleGroup
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsSolvable (seedProjection E).ker := seedProjection_ker_solvable E hstar hmodel
  let r := PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    (seedProjection E) (seedProjection_surjective E)
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (seedImage_twoCore_eq_bot E hstar hmodel e).symm)).trans
      (r.symm.trans e)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
