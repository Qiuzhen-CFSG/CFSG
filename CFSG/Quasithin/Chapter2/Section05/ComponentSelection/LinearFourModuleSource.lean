module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearFourCenterSource
public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphFieldKernel.Source
/-! # Literal exceptional parabolic modules from the original source mark
Apply the proved elementary-center conclusion to the same quotient and its
actual maximal parabolic. This discharges the exceptional covering input in
2.5.7; later Thompson-subgroup geometry remains a separate argument.
Source: Aschbacher--Smith 2.5.7, pp.554--555, and I.2.2(3b), pp.409--410. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
open Matrix.PSL3Four.ElementaryParabolic
open scoped MatrixGroups
private theorem source_center_two (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅) : IsPGroup 2 (center L) := by
  rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
  exact pCore_isPGroup

/-- The actual exceptional parabolic residual has its natural module, with
both the center and its Frattini hypothesis discharged by the source marking. -/
theorem MathieuSourceSetup.linear_four_natural_module
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L ⧸ center L ≃* Matrix.PSL3Four.PSL) (b:Bool) :
    let K₁ := liftedResidual (centerProjection e) b
    IsElementaryAbelian 2 (pCore 2 K₁) ∧ frattini (pCore 2 K₁)=⊥ ∧
    ∃ (q:(K₁ ⧸ pCore 2 K₁)≃*SL(2,Matrix.PSL3Four.F))
      (v:pCore 2 K₁→*Multiplicative (Fin 2→Matrix.PSL3Four.F)),
      Function.Surjective v ∧ v.ker=(center K₁).subgroupOf (pCore 2 K₁) ∧
      (∀ g:K₁,∀ a:pCore 2 K₁,
        v (MulAut.conjNormal g a)=Matrix.SL2.naturalAction Matrix.PSL3Four.F
          (q (QuotientGroup.mk' _ g)) (v a)) ∧
      Function.Injective ((Matrix.SL2.naturalAction Matrix.PSL3Four.F).comp q.toMonoidHom) :=
  source_natural_module e (source_center_two c hG sourceC hempty)
    (MathieuSourceSetup.linear_four_center_frattini c hG sourceC hempty e) b

/-- The entire original maximal-parabolic core is elementary and generated
by its commutators with that same parabolic. -/
theorem MathieuSourceSetup.linear_four_parabolic_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L ⧸ center L ≃* Matrix.PSL3Four.PSL) (b:Bool) :
    let P := liftedParabolic (centerProjection e) b
    IsElementaryAbelian 2 (pCore 2 P) ∧ frattini (pCore 2 P)=⊥ ∧
      ⁅pCore 2 P,(⊤:Subgroup P)⁆=pCore 2 P := by
  let := (c.localSetup hG structural115Input sourceC).quasisimple
  exact source_parabolic_core e (source_center_two c hG sourceC hempty)
    (MathieuSourceSetup.linear_four_center_frattini c hG sourceC hempty e) b

/-- Every original elementary subgroup lifts to an elementary full preimage. -/
theorem MathieuSourceSetup.linear_four_elementary_preimage
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L ⧸ center L ≃* Matrix.PSL3Four.PSL)
    (A:Subgroup Matrix.PSL3Four.PSL) [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 (A.comap (centerProjection e)) :=
  centerProjection_elementary_comap e (source_center_two c hG sourceC hempty)
    (MathieuSourceSetup.linear_four_center_frattini c hG sourceC hempty e) A

/-- The graph-field lift is compatible with the actual marked quotient and
fixes the original covering center pointwise. -/
theorem MathieuSourceSetup.linear_four_graphField
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L ⧸ center L ≃* Matrix.PSL3Four.PSL) :
    ∃ a:MulAut L,
      (∀x,e (QuotientGroup.mk (a x))=
        Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer.graphField (e (QuotientGroup.mk x))) ∧
      (∀x∈center L,a x=x) ∧ a^2=1 := by
  let := (c.localSetup hG structural115Input sourceC).quasisimple
  exact Matrix.PSL3Four.CentralCover.GraphFieldKernel.source_graphField_fixes_center e
    (source_center_two c hG sourceC hempty)
    (MathieuSourceSetup.linear_four_center_frattini c hG sourceC hempty e)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
