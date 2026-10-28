module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLocalV
public import Theory.GroupTheory.CComponent.SolvableSupplement
/-!
# Transporting the factor alpha orbit to its selected component

The global alpha decomposition makes the residual action kernel fix
alpha. Equal original images then give identical conjugate spans, and
therefore the same literal C.1.17 module for the selected component.

Source: Aschbacher–Smith C.1.26 and B.6.10, pp.132 and117.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G D : Type*} [Group G] [Group D]

/-- A factor and its component lift have the same alpha orbit whenever their
literal image is the same and the remaining kernel fixes alpha. -/
theorem conjugateSpan_eq_of_same_image
    (q : G →* D) (E L K : Subgroup G) (hLK : L ≤ K)
    (himage : L.map q = K.map q)
    (hker : K ⊓ q.ker ≤ centralizer (E : Set G)) :
    conjugateSpanBy E L = conjugateSpanBy E K := by
  apply le_antisymm (conjugateSpanBy_mono le_rfl hLK)
  apply (closure_le _).mpr
  rintro x ⟨k,hk,e,he,rfl⟩
  obtain ⟨l,hl,hql⟩ := himage.symm ▸ mem_map_of_mem q hk
  let c := l⁻¹*k
  have hcl : c ∈ K := K.mul_mem (K.inv_mem (hLK hl)) hk
  have hcq : c ∈ q.ker := by
    change q (l⁻¹*k)=1
    rw [map_mul,map_inv,hql,inv_mul_cancel]
  have hc : c*e*c⁻¹=e := by
    rw [←hker ⟨hcl,hcq⟩ e he,mul_assoc,mul_inv_cancel,mul_one]
  have hkc : l*c=k := by dsimp [c]; group
  have hh : k*e*k⁻¹=l*e*l⁻¹ := by
    rw [←hkc,mul_inv_rev]
    calc
      _ = l*(c*e*c⁻¹)*l⁻¹ := by group
      _ = _ := by rw [hc]
  rw [hh]
  exact subset_closure ⟨l,hl,e,he,rfl⟩

/-- The original global alpha decomposition makes each residual factor's
action kernel fix alpha, even when that kernel is not a two-group. -/
theorem factor_kernel_centralizes_alpha
    (T U X K : Subgroup G) (hKX : K ≤ X)
    (q : G →* D) (hk : q.ker ≤ centralizer (U : Set G))
    (ha : thompsonAlpha T ≤ U ⊔ (thompsonAlpha T ⊓ centralizer (X : Set G))) :
    K ⊓ q.ker ≤ centralizer (thompsonAlpha T : Set G) := by
  apply le_centralizer_iff.mp
  apply ha.trans
  apply sup_le
  · exact le_centralizer_iff.mp (inf_le_right.trans hk)
  · intro e he k hk'
    exact he.2 k (hKX hk'.1)

variable [Finite G]
/-- Literal localV consumer for the original Baumann group and selected
component. The previously proved factor orbit is transported unchanged. -/
theorem localV_component_eq_factor_orbit
    (T U X K L : Subgroup G) (hLK : L ≤ K) (hKX : K ≤ X)
    (hBL : baumann T ≤ normalizer (L : Set G))
    (q : G →* D) (hk : q.ker ≤ centralizer (U : Set G))
    (himage : L.map q = K.map q)
    (ha : thompsonAlpha T ≤ U ⊔ (thompsonAlpha T ⊓ centralizer (X : Set G))) :
    (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype = conjugateSpanBy (thompsonAlpha T) K := by
  rw [localV_factor_baumann_map T L hBL]
  exact conjugateSpan_eq_of_same_image q _ L K hLK himage
    (factor_kernel_centralizes_alpha T U X K hKX q hk ha)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
