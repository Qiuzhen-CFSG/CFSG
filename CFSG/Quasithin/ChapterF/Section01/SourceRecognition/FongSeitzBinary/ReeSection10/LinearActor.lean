module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearSection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.EffectiveSections

/-!
# The whole linear actor and supplied reflection

The literal endpoint quotient maps the source root-generated group onto
SL₂(q): its image is the two-generated residual of the model. The central
odd stem kernel vanishes by cyclic odd Sylows and transfer. This retains
the whole actor at q=2. The existing rank-one pinning then aligns the
supplied reflection with the Weyl matrix and proves its square-one relation.
Its reflection--unipotent cubic product will detect the V₁ action kernel.

Source: Fong--Seitz I (5C)--(5D), pp.25--27, and II p.222 before (10.6).
The only source input is the same ReeSixHData; no module action is assumed.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
theorem linearRemainder_le_kernel : simpleRemainder Q split 0 ≤ localKernel Q 0 :=
  remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
    (ReeSource.linear_normalizer_index c.linearSylow)

def linearPanelMarking : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃*
    Matrix.SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m) :=
  (show (Endpoint Q 0 ⧸ panelKernel Q 0) ≃*
    BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup (2*m+1) from
      c.common_field ▸ c.linear).trans (Theory.PSL2.sl2QuotientEquiv _).symm

def linearActorMap : rankOne Q split 0 →*
    Matrix.SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m) :=
  (linearPanelMarking Q split c).toMonoidHom.comp ((QuotientGroup.mk' (panelKernel Q 0)).comp
    (inclusion (rankOne_le_parabolic Q split 0)))

private theorem linear_model_primeToResidual (m : ℕ) :
    primeToResidual 2 (Matrix.SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m)) = ⊤ := by
  exact QuadrangleStructure.linear_cover_primeToResidual_top (MonoidHom.id _)
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_card (n := 0) (by simp))

theorem linearActorMap_ker :
    (linearActorMap Q split c).ker = (RootLocalCover.projection Q split 0).ker := by
  let ν := linearPanelMarking Q split c
  rw [RootLocalCover.projection_ker]
  ext r
  change ν (QuotientGroup.mk' (panelKernel Q 0)
    (inclusion (rankOne_le_parabolic Q split 0) r)) = 1 ↔ _
  rw [← map_one ν, ν.injective.eq_iff]
  change inclusion (rankOne_le_parabolic Q split 0) r ∈
    (QuotientGroup.mk' (panelKernel Q 0)).ker ↔ _
  rw [QuotientGroup.ker_mk']
  change _ ↔ inclusion (rankOne_le_parabolic Q split 0) r ∈
    (localKernel Q 0).subgroupOf (Endpoint Q 0)
  rw [localKernel_subgroupOf]
  rfl

theorem linearActorMap_surjective : Function.Surjective (linearActorMap Q split c) := by
  let ν := linearPanelMarking Q split c
  let f : Endpoint Q 0 →* Matrix.SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m) :=
    ν.toMonoidHom.comp (QuotientGroup.mk' (panelKernel Q 0))
  have hf : Function.Surjective f := ν.surjective.comp (QuotientGroup.mk'_surjective _)
  have hrange : (linearActorMap Q split c).range =
      ((localClosure Q split 0).subgroupOf (Endpoint Q 0)).map f := by
    apply le_antisymm
    · rintro y ⟨r,rfl⟩
      exact ⟨inclusion (rankOne_le_parabolic Q split 0) r,
        rankOne_le_localClosure Q split 0 r.property,rfl⟩
    · rintro y ⟨z,hc,rfl⟩
      have hh := localClosure_le_rankOne_sup_kernel Q split 0
        (linearRemainder_le_kernel Q split c) hc
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
        ((rankOne_le_parabolic Q split 0).trans (localKernel_parabolic_normalizes Q 0))] at hh
      obtain ⟨r,hr,k,hk,he⟩ := hh
      let rE : Endpoint Q 0 := ⟨r,rankOne_le_parabolic Q split 0 hr⟩
      let kE : Endpoint Q 0 := ⟨k,Q.tits.B_le_standardParabolic _ (localKernel_le_borel Q 0 hk)⟩
      have hkE : kE ∈ panelKernel Q 0 := by
        change kE ∈ (endpointBorel Q 0).normalCore
        rw [← localKernel_subgroupOf]
        exact hk
      have heE : z = rE*kE := Subtype.ext he.symm
      have hfk : f kE = 1 := by
        change ν (QuotientGroup.mk' (panelKernel Q 0) kE) = 1
        exact (congrArg ν ((QuotientGroup.eq_one_iff (N := panelKernel Q 0) kE).mpr hkE)).trans ν.map_one
      refine ⟨⟨r,hr⟩,?_⟩
      rw [heE,map_mul,hfk,mul_one]
      rfl
  apply MonoidHom.range_eq_top.mp
  rw [hrange, QuadrangleStructure.localClosure_eq_primeToResidual Q split 0
    (UnitarySource.actorReflection Q split 0), map_primeToResidual_of_surjective 2 f hf,
    linear_model_primeToResidual m]


theorem linearActorMap_injective : Function.Injective (linearActorMap Q split c) := by
  obtain ⟨_,hc,ho,hd⟩ := RootLocalCover.central_odd_cover Q split 0
    (linearRemainder_le_kernel Q split c)
  have hk := linearActorMap_ker Q split c
  exact GTwoSource.odd_stem_linear_injective _ (linearActorMap_surjective Q split c)
    (hk.symm ▸ hc) (hk.symm ▸ hd) (hk.symm ▸ ho)

def linearActorEquiv : rankOne Q split 0 ≃*
    Matrix.SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m) :=
  MulEquiv.ofBijective (linearActorMap Q split c)
    ⟨linearActorMap_injective Q split c,linearActorMap_surjective Q split c⟩

def linearLocalMarking : localGroup Q split 0 ≃* PSL(2,ReeF4.CoefficientField m) :=
  QuadrangleStructure.localGroupEquivOfCenterless Q split 0
    (linearRemainder_le_kernel Q split c)
    ((linearActorEquiv Q split c).trans (Theory.PSL2.sl2QuotientEquiv _))
    BenderSuzuki.ZD.Linear.psl2_center_eq_bot

def linearPinning : Matrix.SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m) ≃*
    rankOne Q split 0 :=
  GTwoSource.alignedPinning Q split 0 (linearRemainder_le_kernel Q split c)
    (linearLocalMarking Q split c) (c.reflections 0)
/-- The supplied linear reflection is an actual involution. -/
theorem linearReflection_sq :
    ((c.reflections 0).val : X ⧸ Q.D) * (c.reflections 0).val = 1 :=
  GTwoSource.sourceReflection_sq Q split 0 (linearRemainder_le_kernel Q split c)
    (linearLocalMarking Q split c) (c.reflections 0)

theorem linearPinning_weyl :
    (linearPinning Q split c (Theory.PSL2.SemilinearCoverage.weyl _) : X ⧸ Q.D) =
      (c.reflections 0).val :=
  GTwoSource.alignedPinningHom_weyl Q split 0 (linearRemainder_le_kernel Q split c)
    (linearLocalMarking Q split c) (c.reflections 0)

/-- Its cubic mover uses the same reflection and a point of the simple root. -/
def linearMover : rankOne Q split 0 :=
  oddProduct Q split 0 (linearRemainder_le_kernel Q split c)
    (linearLocalMarking Q split c) (c.reflections 0)

theorem linearMover_cube : (linearMover Q split c)^3 = 1 :=
  oddProduct_cube Q split 0 (linearRemainder_le_kernel Q split c)
    (linearLocalMarking Q split c) (c.reflections 0)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
