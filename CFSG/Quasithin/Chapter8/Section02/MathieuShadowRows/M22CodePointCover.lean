module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointSection
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.GroupTheory.PCoreImage
public import Theory.Mathieu.M22.CentralCover.HexadPerfect
/-!
# The full original M22 point centralizer

Restrict the original full hexad cover to its perfect residual without
changing its kernel. Whole-code movement puts the full module inside that
residual; surjectivity and the exact module kernel then recover the entire
point centralizer. This supplies the equality and local-core containment
used by the original point-pairing and closure arguments.

Source: Aschbacher--Smith 8.2.11--12, printed p.722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- Restrict the original full hexad cover to its literal perfect residual.
No part of the original covering kernel is discarded. -/
theorem m22_point_full_residual_cover
    (L : Subgroup G) (z : G) {D : Finset (Fin 22)} (hD : D ∈ m22Blocks)
    (c : (L ⊓ centralizer ({z} : Set G) : Subgroup G) →* MulAction.stabilizer M22 D)
    (hc : Function.Surjective c) (hk : IsPGroup 2 c.ker) :
    Function.Surjective (c.comp (inclusion (Centralizer.localResidual_le L z))) ∧
      IsPGroup 2 (c.comp (inclusion (Centralizer.localResidual_le L z))).ker := by
  let C := L ⊓ centralizer ({z} : Set G)
  let R := Centralizer.localResidual L z
  let b : solvableResidual C ≃* R :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let : Group.IsPerfect (MulAction.stabilizer M22 D) := m22HexadStabilizer_isPerfect hD
  have hs : Function.Surjective (c.comp (solvableResidual C).subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype,map_solvableResidual_eq c hc,solvableResidual_eq_top]
  refine ⟨?_,?_⟩
  · intro y
    obtain ⟨x,hx⟩ := hs y
    exact ⟨b x,hx⟩
  · exact hk.comap_of_injective _ (inclusion_injective _)

/-- Once the original full kernel is V, the point residual is the entire
point centralizer and its two-core contains the entire original module. -/
theorem m22_point_full_centralizer
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hVL : V ≤ L) (hLN : L ≤ normalizer (V : Set G))
    {D : Finset (Fin 22)} (hD : D ∈ m22Blocks)
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* MulAction.stabilizer M22 D)
    (hc : Function.Surjective c)
    (hk : c.ker = V.subgroupOf (L ⊓ centralizer ({(z : G)} : Set G)))
    (hz : e (Additive.ofMul z) = m22HexadVector hD)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion (inf_le_left.trans hLN) r)) v) =
        m22CodeRepresentation (c r).val (e v)) :
    Centralizer.localResidual L z = L ⊓ centralizer ({(z : G)} : Set G) ∧
      V ≤ Centralizer.localTwoCore L z ∧
      (c.comp (inclusion (Centralizer.localResidual_le L z))).ker =
        V.subgroupOf (Centralizer.localResidual L z) := by
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let R := Centralizer.localResidual L z
  let i := inclusion (Centralizer.localResidual_le L z)
  let f := c.comp i
  have hkp : IsPGroup 2 c.ker := by
    rw [hk]
    exact (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  obtain ⟨hf,hfk⟩ := m22_point_full_residual_cover L z hD c hc hkp
  have hmove := (m22_point_hexad_section L V z hLN hD e f hf hfk hz
    (fun r v => he (i r) v)).2.2.2
  have hVC : V ≤ C := le_inf hVL (by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨v,hv⟩ : V) z)))
  have hVN : V ≤ normalizer (R : Set G) := hVC.trans (C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (solvableResidual C)))
  have hVR : V ≤ R := hmove.ge.trans (le_normalizer_iff_commutator_le_right.mp hVN)
  have hRC : R = C := by
    apply le_antisymm (Centralizer.localResidual_le L z)
    intro x hx
    obtain ⟨r,hr⟩ := hf (c ⟨x,hx⟩)
    change c (i r) = c ⟨x,hx⟩ at hr
    have hdiff : (⟨x,hx⟩ : C)*(i r)⁻¹ ∈ c.ker := by
      change c ((⟨x,hx⟩ : C)*(i r)⁻¹)=1
      rw [map_mul,map_inv,←hr,mul_inv_cancel]
    have hv : x*(r : G)⁻¹ ∈ V := hk.le hdiff
    have hm := R.mul_mem (hVR hv) r.property
    simpa only [inv_mul_cancel_right] using hm
  refine ⟨hRC,le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVR
    (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN),?_⟩
  ext r
  change c (i r)=1 ↔ (r : G) ∈ V
  exact show i r ∈ c.ker ↔ (r : G) ∈ V from hk ▸ Iff.rfl

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
