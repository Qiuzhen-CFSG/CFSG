module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Kernel

/-!
# The selected omega span with its central fixed summand

An actual moving natural subgroup need not contain the whole Thompson alpha
subgroup: a central direct factor survives in alpha. If its orbit is contained
in the alpha closure, the alpha decomposition identifies the selected local
span as the moving subgroup times the central fixed alpha summand. Its
centralizer and full commutator consequently retain exactly the original
moving subgroup. No canonical-span equality is imposed on that subgroup.

Source: Aschbacher–Smith C.1.21(4) and C.1.24, printed pp.128–131.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open ChapterB ChiProduct.SelectedRankOne
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The fixed alpha factor is retained; only the moving orbit is required
inside the alpha closure. -/
theorem exceptional_alpha_closure (T W L : Subgroup G) [W.Normal] [L.Normal]
    (hgen : L ⊔ T = ⊤)
    (hW : W ≤ normalClosure (thompsonAlpha T : Set G))
    (ha : thompsonAlpha T ≤ W ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    normalClosure (thompsonAlpha T : Set G) =
      W ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)) := by
  let D := thompsonAlpha T ⊓ centralizer (L : Set G)
  have hLD : L ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp (show D ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTD : T ≤ normalizer (D : Set G) :=
    (le_inf (alpha_normalized T) (show T ≤ normalizer (centralizer (L : Set G) : Set G)
      from le_normalizer_of_normal)).trans inf_normalizer_le_normalizer_inf
  let : D.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hLD hTD))
  exact le_antisymm (normalClosure_le_normal ha)
    (sup_le hW (inf_le_left.trans le_normalClosure))

/-- Comparison for the literal inclusion Baum(T) → L Baum(T). -/
theorem exceptional_localV_map (T W L : Subgroup G) [W.Normal] [L.Normal]
    (hgen : L ⊔ T = ⊤)
    (hW : W ≤ normalClosure (thompsonAlpha T : Set G))
    (ha : thompsonAlpha T ≤ W ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    (GlaubermanNiles.localV (inclusion
      (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map (L ⊔ baumann T).subtype =
      W ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)) := by
  rw [localV_selected_baumann_map T L hgen]
  exact exceptional_alpha_closure T W L hgen hW ha

/-- Central fixed alpha does not change the actual local action kernel. -/
theorem exceptional_localKernel (T W L : Subgroup G) [W.Normal] [L.Normal]
    (hgen : L ⊔ T = ⊤)
    (hW : W ≤ normalClosure (thompsonAlpha T : Set G))
    (ha : thompsonAlpha T ≤ W ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    GlaubermanNiles.localKernel (inclusion
      (show baumann T ≤ L ⊔ baumann T from le_sup_right)) =
      (centralizer (W : Set G)).subgroupOf (L ⊔ baumann T) := by
  let N := L ⊔ baumann T
  let e := inclusion (show baumann T ≤ N from le_sup_right)
  have hv := exceptional_localV_map T W L hgen hW ha
  have hWV : W ≤ (GlaubermanNiles.localV e).map N.subtype := by
    rw [hv]
    exact le_sup_left
  ext x
  constructor
  · intro hx w hw
    obtain ⟨v,hv',he⟩ := hWV hw
    have hh := congrArg (fun a : N => (a : G)) (hx v hv')
    change (v : G) * (x : G) = (x : G) * (v : G) at hh
    change (v : G) = w at he
    rwa [he] at hh
  · intro hx v hv'
    have hh : (v : G) ∈ W ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)) := by
      rw [←hv]
      exact mem_map_of_mem N.subtype hv'
    obtain ⟨w,hw,d,hd,hwd⟩ := mem_sup_of_normal_left.mp hh
    apply Subtype.ext
    change (v : G) * (x : G) = (x : G) * (v : G)
    rw [←hwd]
    have hc := ((fixed_alpha_central_selected T L hd) x x.property).symm
    have hwc : w * (x : G) = (x : G) * w := hx w hw
    calc
      (w*d)*(x:G) = w*((x:G)*d) := by rw [mul_assoc,hc]
      _ = (x:G)*(w*d) := by rw [←mul_assoc,hwc,mul_assoc]

/-- Full movement of the original subgroup computes the selected local
commutator without discarding its fixed central factor. -/
theorem exceptional_localV_commutator (T W L : Subgroup G) [W.Normal] [L.Normal]
    (hgen : L ⊔ T = ⊤)
    (hW : W ≤ normalClosure (thompsonAlpha T : Set G))
    (ha : thompsonAlpha T ≤ W ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)))
    (hm : ⁅W,L⁆ = W) :
    (⁅GlaubermanNiles.localV (inclusion
      (show baumann T ≤ L ⊔ baumann T from le_sup_right)),
      (⊤ : Subgroup (L ⊔ baumann T : Subgroup G))⁆).map (L ⊔ baumann T).subtype = W := by
  let D := thompsonAlpha T ⊓ centralizer (L : Set G)
  let N := L ⊔ baumann T
  rw [map_commutator,exceptional_localV_map T W L hgen hW ha,
    ←MonoidHom.range_eq_map,range_subtype]
  change ⁅W ⊔ D,N⁆ = W
  apply le_antisymm
  · apply commutator_le.mpr
    intro v hv n hn
    obtain ⟨w,hw,d,hd,rfl⟩ := mem_sup_of_normal_left.mp hv
    have he : ⁅d,n⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (((fixed_alpha_central_selected T L) hd) n hn).symm
    rw [commutatorElement_mul_left_eq_conj_mul,he]
    simpa only [mul_one,mul_inv_cancel,mul_one,one_mul] using
      (commutator_le_left W N (commutator_mem_commutator hw hn))
  · exact hm.symm.le.trans (commutator_mono le_sup_left le_sup_left)

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
