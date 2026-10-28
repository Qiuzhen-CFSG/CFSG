module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointSection

/-!
# Fixed vectors and fixed cosets for the original M22 point core

The full original residual map sends its two-core onto the native hexad core.
The native fixed line and fixed quotient therefore become, respectively,
C_V(O₂(L_z))=⟨z⟩ and C_{V/⟨z⟩}(O₂(L_z))=V_z/⟨z⟩. The commutator
coordinate formula uses the original ambient elements and the whole code.

Source: Aschbacher--Smith H.16.4(1),(5) and 8.2.11--12, pp.403,722.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.ChiefFlag MathieuCode.Hexad.ChiefFlag.Actions
open M22ChapterH.Hexad.Action
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22PointCoordinates
open ChapterE ChapterH.Section13To16.M22Local.Hexad
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

private theorem native_fixedModulo_iff (v : M22Code) :
    (∀ k : Kernel, m22OuterCodeRepresentation k.val v - v ∈ V1.toSubmodule) ↔
      v ∈ V5.toSubmodule := by
  have h15 : V1.toSubmodule ≤ V5.toSubmodule := NativeSource.code_clauses.1.strict.2.1.le
  have h5 : V5.toSubmodule = codeCommutator Kernel := codeCommutatorSubrepresentation_space
  have hq : fixedCodeQuotient = commutatorImage := NativeSource.code_clauses.2.2.2.2
  have hf : V1.toSubmodule.mkQ v ∈ fixedCodeQuotient ↔
      ∀ k : Kernel, m22OuterCodeRepresentation k.val v - v ∈ V1.toSubmodule := by
    constructor
    · intro hv k
      have hh := hv ⟨inclusion kernel_le_stabilizer k,k.property⟩
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change V1.toSubmodule.mkQ (m22OuterCodeRepresentation k.val v - v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hh
    · intro hv k
      change V1.toSubmodule.mkQ (m22OuterCodeRepresentation k.val.val v) = V1.toSubmodule.mkQ v
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hv ⟨k.val.val,k.property⟩)
  have hm : commutatorImage.comap V1.toSubmodule.mkQ = V5.toSubmodule := by
    change ((codeCommutator Kernel).map V1.toSubmodule.mkQ).comap V1.toSubmodule.mkQ = _
    rw [← h5,Submodule.comap_map_eq,Submodule.ker_mkQ,sup_eq_left.mpr h15]
  calc
    _ ↔ V1.toSubmodule.mkQ v ∈ fixedCodeQuotient := hf.symm
    _ ↔ V1.toSubmodule.mkQ v ∈ commutatorImage := by rw [hq]
    _ ↔ v ∈ V5.toSubmodule := by
      change v ∈ commutatorImage.comap V1.toSubmodule.mkQ ↔ _
      rw [hm]

variable (L : Subgroup G) (z : G)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)

/-- The literal original core maps onto the full native core, via the whole residual map. -/
def coreMap : Centralizer.localTwoCore L z →* Kernel :=
  let q := (m22ToPairStabilizer.comp M22ChapterH.Hexad.Action.Inner.subtype).comp
    (f.comp (inclusion (Centralizer.localTwoCore_le L z)))
  q.codRestrict Kernel (fun x => (m22_point_core_range L z f hf hk) ▸ (show q x ∈ q.range from ⟨x,rfl⟩))

@[simp] theorem coreMap_coe (x : Centralizer.localTwoCore L z) :
    (coreMap L z f hf hk x).val =
      m22ToPairStabilizer (f (inclusion (Centralizer.localTwoCore_le L z) x)).val := rfl

theorem coreMap_surjective : Function.Surjective (coreMap L z f hf hk) := by
  intro k
  have hm : k.val ∈ ((m22ToPairStabilizer.comp M22ChapterH.Hexad.Action.Inner.subtype).comp
      (f.comp (inclusion (Centralizer.localTwoCore_le L z)))).range :=
    (m22_point_core_range L z f hf hk).symm ▸ k.property
  obtain ⟨x,hx⟩ := hm
  exact ⟨x,Subtype.ext hx⟩

variable (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v))

include hf hk he

/-- Pointwise core equivariance, retaining the original ambient conjugation. -/
theorem coreMap_equivariant (x : Centralizer.localTwoCore L z) (v : V) :
    e (Additive.ofMul (⟨(x : G)*(v : G)*(x : G)⁻¹,
      le_normalizer_iff.mp (((Centralizer.localTwoCore_le L z).trans
        ((Centralizer.localResidual_le L z).trans inf_le_left)).trans hLN)
          x x.property v v.property⟩ : V)) =
      m22OuterCodeRepresentation (coreMap L z f hf hk x).val (e (Additive.ofMul v)) :=
  he (inclusion (Centralizer.localTwoCore_le L z) x) (Additive.ofMul v)

/-- The original ambient commutator has the literal native displacement coordinates. -/
theorem coreMap_commutator (x : Centralizer.localTwoCore L z) (v : V) :
    ∃ hv : ⁅(x : G),(v : G)⁆ ∈ V,
      e (Additive.ofMul (⟨⁅(x : G),(v : G)⁆,hv⟩ : V)) =
        m22OuterCodeRepresentation (coreMap L z f hf hk x).val (e (Additive.ofMul v)) -
          e (Additive.ofMul v) := by
  have hc := le_normalizer_iff.mp (((Centralizer.localTwoCore_le L z).trans
    ((Centralizer.localResidual_le L z).trans inf_le_left)).trans hLN)
      x x.property v v.property
  refine ⟨V.mul_mem hc (V.inv_mem v.property),?_⟩
  have hh : (⟨⁅(x : G),(v : G)⁆,V.mul_mem hc (V.inv_mem v.property)⟩ : V) =
      (⟨(x : G)*(v : G)*(x : G)⁻¹,hc⟩ : V) * v⁻¹ :=
    Subtype.ext (commutatorElement_def _ _)
  rw [hh]
  rw [ofMul_mul,ofMul_inv,← sub_eq_add_neg,map_sub,
    coreMap_equivariant L z f hf hk V hLN e he]

/-- The full original core fixes precisely the native fixed line. -/
theorem fixed_coordinates (v : V) :
    (v : G) ∈ centralizer (Centralizer.localTwoCore L z : Set G) ↔
      e (Additive.ofMul v) ∈ V1.toSubmodule := by
  constructor
  · intro hv k
    obtain ⟨x,rfl⟩ := coreMap_surjective L z f hf hk k
    have hh : (x : G)*(v : G)*(x : G)⁻¹ = v :=
      mul_inv_eq_iff_eq_mul.mpr (hv x x.property)
    exact (coreMap_equivariant L z f hf hk V hLN e he x v).symm.trans
      (congrArg (fun w : V => e (Additive.ofMul w)) (Subtype.ext hh))
  · intro hv x hx
    let a : Centralizer.localTwoCore L z := ⟨x,hx⟩
    have hh := (coreMap_equivariant L z f hf hk V hLN e he a v).trans
      (hv (coreMap L z f hf hk a))
    have heq := congrArg (fun w : Additive V => (w.toMul : G)) (e.injective hh)
    exact mul_inv_eq_iff_eq_mul.mp heq

/-- The original central vector generates the entire core-fixed subgroup. -/
theorem fixed_eq_line (hzV : z ∈ V)
    (hz : e (Additive.ofMul (⟨z,hzV⟩ : V)) = m22HexadVector m22Hexad24Ten_mem) :
    V ⊓ centralizer (Centralizer.localTwoCore L z : Set G) = zpowers z := by
  apply le_antisymm
  · intro v hv
    exact (m22_point_line_coordinates V ⟨z,hzV⟩ e hz (Additive.ofMul ⟨v,hv.1⟩)).mpr
      ((fixed_coordinates L z f hf hk V hLN e he ⟨v,hv.1⟩).mp hv.2)
  · intro v hv
    have hvV : v ∈ V := (zpowers_le.mpr hzV) hv
    exact ⟨hvV,(fixed_coordinates L z f hf hk V hLN e he ⟨v,hvV⟩).mpr
      ((m22_point_line_coordinates V ⟨z,hzV⟩ e hz (Additive.ofMul ⟨v,hvV⟩)).mp hv)⟩

/-- Fixing modulo the original central line characterizes the literal original Vz. -/
theorem fixed_modulo_line (hzV : z ∈ V)
    (hz : e (Additive.ofMul (⟨z,hzV⟩ : V)) = m22HexadVector m22Hexad24Ten_mem)
    (v : V) :
    (∀ x : Centralizer.localTwoCore L z, ⁅(x : G),(v : G)⁆ ∈ zpowers z) ↔
      (v : G) ∈ Centralizer.commutatorSpace L V z := by
  have hC : (v : G) ∈ Centralizer.commutatorSpace L V z ↔
      e (Additive.ofMul v) ∈ V5.toSubmodule :=
    m22_point_residual_commutator_coordinates L V z hLN e f hf hk he (Additive.ofMul v)
  apply Iff.trans ?_ hC.symm
  rw [← native_fixedModulo_iff]
  constructor
  · intro hv k
    obtain ⟨x,rfl⟩ := coreMap_surjective L z f hf hk k
    obtain ⟨hc,hcoord⟩ := coreMap_commutator L z f hf hk V hLN e he x v
    rw [← hcoord]
    exact (m22_point_line_coordinates V ⟨z,hzV⟩ e hz (Additive.ofMul ⟨_,hc⟩)).mp (hv x)
  · intro hv x
    obtain ⟨hc,hcoord⟩ := coreMap_commutator L z f hf hk V hLN e he x v
    apply (m22_point_line_coordinates V ⟨z,hzV⟩ e hz (Additive.ofMul ⟨_,hc⟩)).mpr
    rw [hcoord]
    exact hv (coreMap L z f hf hk x)

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22PointCoordinates
