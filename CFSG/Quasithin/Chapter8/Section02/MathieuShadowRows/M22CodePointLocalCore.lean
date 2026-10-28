module
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions
public import Theory.Mathieu.M22.Properties.OuterHexadRadical
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreInRestriction
/-!
# The original M22 point-local two-core

The actual LT action has its full two-core as kernel. The image of L_z is
the inner stabilizer of the original hexad, while the Sylow join lies in
the full design stabilizer. The native radical theorem, including outer
automorphisms, gives identical core images. Lifting through the retained
kernel proves O₂(L_z T)=O₂(L_z) O₂(LT).

Source: Aschbacher--Smith 8.2.11(4) and 8.2.12, printed p.722,
refs/quasithin.pdf. The original Chapter12 marking supplies the actual
join action; no faithful quotient is substituted for its full kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The original point-local join has exactly the hexad core times the
full LT-core, including the possible outer action. -/
theorem m22_point_local_core_product
    (L : Subgroup G) (T : Sylow 2 G) (z : G)
    (hTR : (T : Subgroup G) ≤ normalizer (Centralizer.localResidual L z : Set G))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G) →* m22DesignAut)
    (hak : a.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (hR : ((Centralizer.localResidual L z).subgroupOf (L ⊔ (T : Subgroup G))).map a =
      (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion)
    (hRT : ((Centralizer.localResidual L z ⊔ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).map a ≤ MulAction.stabilizer m22DesignAut B) :
    (Centralizer.localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 =
      Centralizer.localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let R := Centralizer.localResidual L z
  have hRL : R ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  have hRJ : R ≤ J := hRL.trans le_sup_left
  have hap : IsPGroup 2 a.ker := hak ▸ pCore_isPGroup
  let im := fun A : Subgroup G => (A.subgroupOf J).map a
  have himcore (A : Subgroup G) (hAJ : A ≤ J) : im (A.pCoreIn 2) = (im A).pCoreIn 2 := by
    dsimp only [im]
    rw [←pCoreIn_subgroupOf 2 A J hAJ,map_pCoreIn_of_ker_isPGroup a hap]
  have hile : im R ≤ im (R ⊔ (T : Subgroup G)) := map_mono (comap_mono le_sup_left)
  have hsame : im ((R ⊔ (T : Subgroup G)).pCoreIn 2) = im (R.pCoreIn 2) := by
    rw [himcore _ (sup_le hRJ le_sup_right),himcore R hRJ]
    exact (M22OuterHexad.radical_eq hB _ (hR.symm.le.trans hile) hRT).trans
      (M22OuterHexad.radical_eq hB _ hR.ge (hile.trans hRT)).symm
  apply le_antisymm
  · intro x hx
    have hxJ : x ∈ J := (pCoreIn_le 2 _).trans (sup_le hRJ le_sup_right) hx
    have hximage : a ⟨x,hxJ⟩ ∈ im (R.pCoreIn 2) := hsame ▸ mem_map_of_mem a hx
    obtain ⟨y,hy,heq⟩ := hximage
    have hxy : (⟨x,hxJ⟩ : J) * y⁻¹ ∈ pCore 2 J := by
      rw [←hak]
      change a ((⟨x,hxJ⟩ : J)*y⁻¹)=1
      rw [map_mul,map_inv,heq,mul_inv_cancel]
    have hxy' : x*(y : G)⁻¹ ∈ J.pCoreIn 2 := mem_map_of_mem J.subtype hxy
    have hp := (R.pCoreIn 2 ⊔ J.pCoreIn 2).mul_mem (mem_sup_right hxy') (mem_sup_left hy)
    change x*(y : G)⁻¹*(y : G) ∈ _ at hp
    simpa only [R,J,Centralizer.localTwoCore,Subgroup.pCoreIn,mul_assoc,inv_mul_cancel,mul_one] using hp
  · apply sup_le
    · exact pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer hTR)
    · have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
        simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
          (show (T : Subgroup G) ≤ J from le_sup_right)] using
          pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
      intro x hx
      exact inf_pCoreIn_le_of_le 2 (sup_le hRJ le_sup_right) ⟨mem_sup_right (hQT hx),hx⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
