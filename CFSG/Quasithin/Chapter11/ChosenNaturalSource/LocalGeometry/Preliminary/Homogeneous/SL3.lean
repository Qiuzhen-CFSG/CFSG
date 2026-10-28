module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Sylow
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# Homogeneity of the full chosen-natural linear-three quotient

Every automorphism of the full SL₃ group is linear-field or linear-field
followed by the fixed opposition graph automorphism. Linear-field factors
have actual binary natural intertwiners. Thus there are at most two types;
the chosen Sylow-invariant seed forces just one type under the normalizer.
The full SL₃ center is retained in the automorphism lifting and marking.

Source: Aschbacher--Smith, 11.0.3(2), printed p.760.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous
open Matrix.PSL3.OuterSolvable Matrix.PSL3.CartanActions.SixCommutators
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private def coefficientEquiv (F : Type*) [Field F] [Algebra (ZMod 2) F]
    (φ : F ≃+* F) : (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F) where
  toFun v i := φ (v i)
  invFun v i := φ.symm (v i)
  left_inv v := by ext i; exact φ.symm_apply_apply _
  right_inv v := by ext i; exact φ.apply_symm_apply _
  map_add' v w := by ext i; exact φ.map_add _ _
  map_smul' c v := by ext i; exact ZMod.map_smul φ c (v i)

private theorem sl3_linearField_twist (F : BinaryField)
    (g : GL (Fin 3) F.Carrier) (φ : F.Carrier ≃+* F.Carrier) :
    ∃ e : (Fin 3 → F.Carrier) ≃ₗ[ZMod 2] (Fin 3 → F.Carrier),
      ∀ x v, e (linearNatural F 3 x v) =
        linearNatural F 3 ((linearConjSL F.Carrier g * Atlas.fieldEquivSL 3 φ) x) (e v) := by
  let c := coefficientEquiv F.Carrier φ
  let b := (LinearMap.GeneralLinearGroup.toLinearEquiv (GeneralLinearGroup.toLin g)).restrictScalars (ZMod 2)
  refine ⟨c.trans b, ?_⟩
  intro x v
  have hc : c (x.val.mulVec v) = (Atlas.fieldEquivSL 3 φ x).val.mulVec (c v) := by
    ext i
    change φ (∑ j, x.val i j * v j) = ∑ j, φ (x.val i j) * φ (v j)
    simp only [map_sum, map_mul]
  have hg : (linearConjSL F.Carrier g (Atlas.fieldEquivSL 3 φ x)).val * g.val =
      g.val * (Atlas.fieldEquivSL 3 φ x).val := by
    have hh := congrArg (fun y : GL (Fin 3) F.Carrier => (y * g).val)
      (linearConjSL_toGL F.Carrier g (Atlas.fieldEquivSL 3 φ x))
    simp only [mul_assoc, inv_mul_cancel, mul_one] at hh
    simpa only [GeneralLinearGroup.coe_mul, SpecialLinearGroup.coe_GL_coe_matrix] using hh
  change g.val.mulVec (c (x.val.mulVec v)) =
    (linearConjSL F.Carrier g (Atlas.fieldEquivSL 3 φ x)).val.mulVec (g.val.mulVec (c v))
  rw [hc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

/-- Source 11.0.3(2) for the full SL₃ row, with unchanged quotient and action. -/
theorem fullModule_sl3_homogeneous
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      (∃ I : Subrepresentation (σ.comp (L.subgroupOf M).subtype),
        IsIrreducible I.toRepresentation ∧ homogeneousPart I ⊤ = ⊤) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  apply fullModule_homogeneous_of_normalizer_twists D S
  apply normalizer_twists_of_two_model_types D S m (oppositionGraphSL S.field.Carrier)
  intro a
  obtain ⟨g, φ, ε, ha⟩ := Matrix.PSL3.CartanActions.ActorCoverage.specialCoverage_of_standard_eq_top
    S.field.Carrier (standard_eq_top_of_two_power_card S.field.Carrier
      S.field.degree_pos S.field.card_eq) a
  obtain ⟨b, hb⟩ := sl3_linearField_twist S.field g φ
  cases ε
  · left
    refine ⟨b, ?_⟩
    simpa only [ha, specialActor, Bool.false_eq_true, ↓reduceIte, mul_one] using hb
  · right
    refine ⟨b, ?_⟩
    simpa only [ha, specialActor, ↓reduceIte, mul_inv_cancel_right] using hb

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
