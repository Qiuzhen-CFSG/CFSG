module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphSylowModel
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The original point endpoint's graph centralizer

The fixed vector-local group has a graph-fixed Heisenberg kernel of order
eight and quotient SL2 of the binary fixed field, of order six. A graph-fixed
point-parabolic element has its first scalar in the binary field, hence that
scalar is one and the element is already vector-local. The graph centralizer
in the doubled point endpoint is therefore the direct product of this order48
fixed local group and the same graph C2.

Transport through the literal projective map and source endpoint gives
|E1|=96 and makes the previously counted Tf of order32 a Sylow subgroup of E1.
This discharges the point-Sylow input to the original exceptional root-moving
normalizer argument. No endpoint-recognition premise remains in either count.

Source: Aschbacher--Smith F.4.37 and F.5.3, printed pp.293 and 300.
-/

@[expose] public noncomputable section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => localSU F (form F σ hσ)
local notation "K" => FixedBy.subfield F σ
local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "PX" => UnitaryFourOuter.point F σ hσ
local notation "X" => UnitaryFourOuter.Extension F σ hσ

theorem graphFixedLocal_card : Nat.card graphFixedLocal = 48 := by
  have hc := graphFixedMiddle.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr graphFixedMiddle_surjective,
    card_top,graphFixedMiddle_ker_card,Atlas.card_sl_two] at hc
  change 8 * (Nat.card (PointLocal.FixedField 1) *
    (Nat.card (PointLocal.FixedField 1) ^ 2 - 1)) = _ at hc
  rw [PointLocal.fixedField_card 1 hn] at hc
  exact hc.symm

def graphFixedPoint : Subgroup P :=
  ((UnitaryFourOuter.matrixHom F σ hσ).comp (P).subtype).eqLocus (P).subtype

private theorem fixedPoint_mem_local (a : graphFixedPoint) : a.val.val ∈ L := by
  apply (mem_localSU F _ _).mpr
  refine ⟨?_, (mem_pointParabolicSU F _ a.val.val).mp a.val.property⟩
  have hf : σ (pointScalar F (form F σ hσ) a.val) = pointScalar F (form F σ hσ) a.val :=
    congrArg (fun x : SU F (form F σ hσ) => x.val.val 0 0) a.property
  let x : K := ⟨pointScalar F (form F σ hσ) a.val,hf⟩
  have hx : x ≠ 0 := by
    intro he
    exact Units.ne_zero ((pointScalar F (form F σ hσ)).toHomUnits a.val)
      (congrArg Subtype.val he)
  have hk : Nat.card K = 2 := by simpa using PointLocal.fixedField_card 1 hn
  have he : x = 1 := ((Nat.card_eq_two_iff' (0 : K)).mp hk).unique hx one_ne_zero
  exact congrArg Subtype.val he

/-- Fixing the graph involution removes the odd point scalar, with the same
matrix entries on the actual vector-local subgroup. -/
def graphFixedPointEquivLocal : graphFixedPoint ≃* graphFixedLocal where
  toFun a := ⟨⟨a.val.val,by exact fixedPoint_mem_local a⟩,a.property⟩
  invFun a := ⟨⟨a.val.val,localSU_le_pointParabolicSU F _ a.val.property⟩,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def matrixPointGraphElement : PX :=
  ⟨UnitaryFourOuter.sigma F σ hσ,(P).one_mem⟩

def matrixPointGraph : Subgroup PX := centralizer ({matrixPointGraphElement} : Set PX)

private theorem point_commutes_graph_iff (a : PX) :
    a ∈ matrixPointGraph ↔
      UnitaryFourOuter.matrixHom F σ hσ a.val.left = a.val.left := by
  rw [matrixPointGraph,mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he := congrArg (fun x : PX => x.val.left) h
    simpa [matrixPointGraphElement,UnitaryFourOuter.sigma,
      UnitaryFourOuter.action_generator,UnitaryFourOuter.matrixAut] using he.symm
  · intro h
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simpa [matrixPointGraphElement,UnitaryFourOuter.sigma,
        UnitaryFourOuter.action_generator,UnitaryFourOuter.matrixAut] using h.symm
    · change a.val.right * UnitaryFourOuter.generator = UnitaryFourOuter.generator * a.val.right
      exact mul_comm _ _

private theorem action_fixed (a : UnitaryFourOuter.C2) (b : graphFixedPoint) :
    UnitaryFourOuter.action F σ hσ a b.val.val = b.val.val := by
  rcases UnitaryFourOuter.c2_cases a with ha | ha
  · simp [ha]
  · rw [ha,UnitaryFourOuter.action_generator]
    exact b.property

/-- The graph centralizer in the literal doubled point endpoint is the direct
product of the ordinary fixed group and the same graph C2. -/
def matrixPointGraphEquiv : matrixPointGraph ≃* graphFixedPoint × UnitaryFourOuter.C2 where
  toFun a := (⟨⟨a.val.val.left,a.val.property⟩,by exact (point_commutes_graph_iff _).mp a.property⟩,
    a.val.val.right)
  invFun a := ⟨⟨⟨a.1.val.val,a.2⟩,a.1.val.property⟩,
    by exact (point_commutes_graph_iff _).mpr a.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      change a.val.val.left * UnitaryFourOuter.action F σ hσ a.val.val.right b.val.val.left =
        a.val.val.left * b.val.val.left
      rw [action_fixed a.val.val.right
        ⟨⟨b.val.val.left,b.val.property⟩,(point_commutes_graph_iff _).mp b.property⟩]
    · rfl

private theorem point_graph_projection :
    Extension.binaryPointMatrixEquiv matrixPointGraphElement = modelGraph false := by
  apply Subtype.ext
  exact Extension.extensionProjection_sigma 1 hn

/-- The same model centralizer is transported through the injective projective
map; the specified graph involution is preserved. -/
def modelPointGraphEquiv :
    centralizer ({modelGraph false} : Set (modelEndpoint false)) ≃* matrixPointGraph := by
  let e := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
    Extension.binaryPointMatrixEquiv matrixPointGraphElement
  exact (e.trans (MulEquiv.subgroupCongr (by rw [point_graph_projection]; rfl))).symm

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- The actual source E1 is the direct product of the ordinary fixed vector
local group and the marked graph C2. -/
def source_E_point_equiv_fixedLocal (hi : Function.Injective i) :
    E c i false ≃* graphFixedLocal × UnitaryFourOuter.C2 := by
  let e := (centralizer ({modelGraph false} : Set (modelEndpoint false))).equivMapOfInjective
    (endpointMap c i false) (endpointMap_injective c i hi false)
  exact ((e.trans (MulEquiv.subgroupCongr (E_eq_map_centralizer c i hi false).symm)).symm.trans
    modelPointGraphEquiv).trans (matrixPointGraphEquiv.trans
      (MulEquiv.prodCongr graphFixedPointEquivLocal (MulEquiv.refl _)))

/-- The original point endpoint's graph centralizer has order96, without any
endpoint-recognition premise. -/
theorem source_E_point_card (hi : Function.Injective i) : Nat.card (E c i false) = 96 := by
  rw [Nat.card_congr (source_E_point_equiv_fixedLocal c i hi).toEquiv,
    Nat.card_prod,graphFixedLocal_card]
  change 48 * Nat.card (ZMod 2) = 96
  norm_num

/-- The original Tf is Sylow in E1. This removes the local Sylow premise in
the source root-moving normalizer construction. -/
theorem source_Tf_sylow_point (hi : Function.Injective i) :
    ∃ S : Sylow 2 (E c i false),
      (S : Subgroup (E c i false)).map (E c i false).subtype = TfImage c i :=
  source_Tf_sylow_of_endpoint_card c i hi false (source_E_point_card c i hi)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
