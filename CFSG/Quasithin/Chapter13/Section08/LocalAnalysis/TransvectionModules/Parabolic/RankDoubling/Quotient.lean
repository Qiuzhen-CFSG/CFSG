module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The literal quotient and three-space orbit in 13.8.6

The elementary seed V generates U₂ inside the abelian group V_H of
13.8.2. Thus U₂ is elementary abelian, V₂ is relatively normal, and
U₂/V₂ has its canonical binary vector-space structure. The flag supplies
V₂ ≤ U₂. The subspace W is the span of the actual K₂-conjugates of V₃
in this quotient; it also equals the image of their generated subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6, printed p.948. K₂ and U₂ are exactly the definitions from Basic.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
variable {G : Type*} [Group G]

/-- The elementary structure follows from abelianness and the elementary seed. -/
theorem elementary_conjugateSpan (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V A)] :
    IsElementaryAbelian 2 (conjugateSpanBy V A) := by
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  suffices hp : ∀ y ∈ conjugateSpanBy V A, y ^ 2 = 1 by
    intro x
    exact Subtype.ext (hp x x.property)
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, _, v, hv, rfl⟩ := hy
    simpa using congrArg (MulAut.conj a) (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)
  | one => simp
  | mul x y hx hy hxp hyp =>
    rw [(show Commute x y from setLike_mul_comm (s := conjugateSpanBy V A) hx hy).mul_pow, hxp, hyp,
      mul_one]
  | inv x _ hxp => rw [inv_pow, hxp, inv_one]

/-- `U₂` is inside the abelian source group `V_H`. -/
theorem U2_le_VH (H V V₂ : Subgroup G) : Source.U2 H V V₂ ≤ Source.VH H V :=
  conjugateSpanBy_mono le_rfl (Source.K2_le H V₂)

variable (H V V₂ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

instance U2_commutative : IsMulCommutative (Source.U2 H V V₂) :=
  IsMulCommutative.of_setLike_mul_comm fun _ hx _ hy =>
    setLike_mul_comm (U2_le_VH H V V₂ hx) (U2_le_VH H V V₂ hy)

instance U2_elementary : IsElementaryAbelian 2 (Source.U2 H V V₂) :=
  by
    let : IsMulCommutative (conjugateSpanBy V (Source.K2 H V₂)) := U2_commutative H V V₂
    exact elementary_conjugateSpan V (Source.K2 H V₂)

omit [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)] in
/-- The flag supplies the actual containment, rather than an implicit intersection. -/
theorem V2_le_U2 (hflag : V₂ ≤ V) : V₂ ≤ Source.U2 H V V₂ :=
  hflag.trans (Source.seed_le_U2 H V V₂)

omit [IsElementaryAbelian 2 V] in
/-- Normality is relative to `U₂`, never normality in the ambient simple group. -/
theorem V2_normal : (V₂.subgroupOf (Source.U2 H V V₂)).Normal := inferInstance

/-- The literal quotient occurring after 13.8.6(3). -/
abbrev Uhat := Source.U2 H V V₂ ⧸ V₂.subgroupOf (Source.U2 H V V₂)

/-- The canonical binary quotient map. -/
def quotientMap : Additive (Source.U2 H V V₂) →ₗ[ZMod 2] Additive (Uhat H V V₂) :=
  (QuotientGroup.mk' (V₂.subgroupOf (Source.U2 H V V₂))).toAdditive.toZModLinearMap 2

@[simp] theorem quotientMap_eq_zero (x : Additive (Source.U2 H V V₂)) :
    quotientMap H V V₂ x = 0 ↔ (x.toMul : G) ∈ V₂ :=
  QuotientGroup.eq_one_iff x.toMul

/-- The span of all actual conjugates of the source three-space modulo `V₂`. -/
def W (V₃ : Subgroup G) (h₃ : V₃ ≤ V) : Submodule (ZMod 2) (Additive (Uhat H V V₂)) :=
  Submodule.span (ZMod 2) {x | ∃ k : Source.K2 H V₂, ∃ v : V₃,
    x = quotientMap H V V₂ (Additive.ofMul
      ⟨(k : G) * (v : G) * (k : G)⁻¹,
        Subgroup.subset_closure ⟨k, k.property, v, h₃ v.property, rfl⟩⟩)}

omit [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)] in
/-- The three-space orbit lies simultaneously in `U_H` and in `U₂`. -/
theorem threeOrbit_le (V₃ : Subgroup G) (h₃ : V₃ ≤ V) :
    conjugateSpanBy V₃ (Source.K2 H V₂) ≤ Source.UH H V₃ ⊓ Source.U2 H V V₂ :=
  le_inf (conjugateSpanBy_mono le_rfl (Source.K2_le H V₂))
    (conjugateSpanBy_mono h₃ le_rfl)

/-- The definition of W agrees with the image of the generated subgroup.
This gives a bridge for first-isomorphism and model-quotient transports. -/
theorem W_eq_image_span (V₃ : Subgroup G) (h₃ : V₃ ≤ V) :
    W H V V₂ V₃ h₃ =
      (AddSubgroup.toZModSubmodule (n := 2)
        ((conjugateSpanBy V₃ (Source.K2 H V₂)).subgroupOf
          (Source.U2 H V V₂)).toAddSubgroup).map (quotientMap H V V₂) := by
  let B := conjugateSpanBy V₃ (Source.K2 H V₂)
  let S := AddSubgroup.toZModSubmodule (n := 2)
    (B.subgroupOf (Source.U2 H V V₂)).toAddSubgroup
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨k, v, rfl⟩
    apply Submodule.mem_map_of_mem
    exact Subgroup.subset_closure ⟨k, k.property, v, v.property, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    change (y.toMul : G) ∈ B at hy
    have hBU := (threeOrbit_le H V V₂ V₃ h₃).trans inf_le_right
    have hall : ∀ (z : G) (hz : z ∈ B),
        quotientMap H V V₂ (Additive.ofMul ⟨z, hBU hz⟩) ∈ W H V V₂ V₃ h₃ := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨k, hk, v, hv, rfl⟩ := hz
        exact Submodule.subset_span ⟨⟨k,hk⟩,⟨v,hv⟩,rfl⟩
      | one => exact (W H V V₂ V₃ h₃).zero_mem
      | mul a b ha hb ha' hb' =>
        exact (W H V V₂ V₃ h₃).add_mem ha' hb'
      | inv a ha ha' => exact (W H V V₂ V₃ h₃).neg_mem ha'
    exact hall y.toMul hy
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
