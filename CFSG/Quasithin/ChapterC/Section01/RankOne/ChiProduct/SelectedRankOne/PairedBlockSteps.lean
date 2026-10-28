module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.BlockSelection
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FactorOrbit
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayer
/-!
# The selected component remains the actual outside block

The two-residual of the original component–Baumann join maps to the
selected component. Its local characteristic-pair block therefore gives
an ambient chi-block. The original Sylow orbit generates the full
residual, preventing that component from lying in a proper control
subgroup.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
theorem selected_component_residual_map
    (T : Sylow 2 G) (L : Subgroup G) (hL : IsPPerfect 2 L)
    (hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (pResidual 2 (L ⊔ baumann (T : Subgroup G) : Subgroup G)).map
      (L ⊔ baumann (T : Subgroup G)).subtype = L := by
  let B := baumann (T : Subgroup G)
  let N := L ⊔ B
  let A := L.subgroupOf N
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hBL)
  have hpA : IsPPerfect 2 A := hL.of_surjective
    (subgroupOfEquivOfLe (show L ≤ N from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show L ≤ N from le_sup_left)).symm.surjective
  have hs : A ⊔ B.subgroupOf N = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L ≤ N from le_sup_left),
      map_subgroupOf_eq_of_le (show B ≤ N from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hr : pResidual 2 N = A := pResidual_eq_of_isPPerfect_sup A (B.subgroupOf N)
    hpA (T.isPGroup'.to_le (show B ≤ T from inf_le_left)).comap_subtype hs
  change (pResidual 2 N).map N.subtype = L
  rw [hr,map_subgroupOf_eq_of_le (show L ≤ N from le_sup_left)]

omit [Finite H] in
theorem selected_component_chi_of_blockAlternative
    (T : Sylow 2 G) (L : Subgroup G) (hL : L.IsCComponent) (hp : IsPPerfect 2 L)
    (hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : BlockAlternative (L ⊔ baumann (T : Subgroup G) : Subgroup G)) : IsChiBlockIn L := by
  let N := L ⊔ baumann (T : Subgroup G)
  let e := ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr (selected_component_residual_map T L hp hBL))
  have hc : IsChiBlock (pResidual 2 N) := by
    rcases hb.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨3,by decide,h⟩
  let := hL.perfect
  exact ⟨⟨inferInstance,RankOne.Solvable.isShort_of_equiv e hb.1.short,hL.subnormal⟩,chi_of_equiv e hc⟩

theorem selected_component_outside_control
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (Y A : Subgroup H) [Y.Normal]
    (hJA : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ Y)
    (hYA : Y ≤ normalizer (A : Set H))
    (L : Subgroup G) (hL : L.IsCComponent)
    (hcan : (solvableResidual (A.comap q)).map (A.comap q).subtype = L)
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hM : M ≠ ⊤) : ¬ L ≤ M := by
  let Q := Y.comap q
  let := hL.perfect
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL.ne_bot
  have hn : Q ≤ normalizer (L : Set G) := selected_component_normalized q A L Q hcan
    ((map_comap_le q Y).trans hYA)
  have hres : pResidual 2 G ≤ Q := map_le_iff_le_comap.mp
    (RankOneBaumann.residual_image_le_normal_thompson_layer T hP U hU hJ q hq hk Y hJA)
  have hgen : Q ⊔ (T : Subgroup G) = ⊤ := top_unique
    ((pResidual_sup_sylow_eq_top T).symm.le.trans (sup_le_sup_right hres _))
  have horbit := source_factor_orbit_eq_residual T hP Q L hn hgen
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  have hTM : (T : Subgroup G) ≤ M := T.toSubgroup.le_normalizer.trans
    ((normalizer_le_characteristicNormalizerClosure_self (T : Subgroup G) hTne).trans hcpu)
  intro hLM
  have hRM : pResidual 2 G ≤ M := by
    rw [←horbit]
    apply iSup_le
    intro t
    rintro x ⟨l,hl,rfl⟩
    change (t:G)*l*(t:G)⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem (hTM t.property) (hLM hl)) (M.inv_mem (hTM t.property))
  exact hM (top_unique ((pResidual_sup_sylow_eq_top T).symm.le.trans (sup_le hRM hTM)))
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
