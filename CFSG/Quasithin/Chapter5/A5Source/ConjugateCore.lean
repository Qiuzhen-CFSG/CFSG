module
public import CFSG.Quasithin.Chapter5.A5Source.BlockEscape
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Saturation
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Saturation
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section06.GeneralLocal
public import Stellmacher.SectionTwo.CubicSelectedQuotient

/-!
# The original C.6.3 conjugate in the A5 Baumann escape

E.2.3 saturation puts the literal core Q=O2(L Baum(T)) in Baum(T).
The alternating-block centralizer theorem splits Q over the original V.
The normalizer obstruction then supplies a conjugate of V escaping Q,
with its conjugator in the full original Baumann normalizer.
Source: Aschbacher--Smith 5.1.7(1), printed pp.633--634, using C.1.13 and C.6.3.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
open ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem baumann_core_le_of_escape
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ≤ baumann (T : Subgroup G) := by
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  have hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) :=
    fun hc => hout (baumann_normalizer_of_thompson_centralizes d hc)
  let := d.reduced.normal
  let := d.reduced.elementary
  let R := T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)
  have hq := d.localActor_surjective_of_thompson_moves hJ
  let f := d.localModuleCoordinates.symm
  have hk : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation (V.subgroupOf (L ⊔ (T : Subgroup G)))
        d.localActor hq d.localActor_kernel g v = v := by
    intro v hv _ _
    have hz : v = 0 := f.injective (hv.trans (map_zero f).symm)
    subst v
    exact map_zero _
  have hs := (SymmetricFive.source_alpha_and_saturation R (local_minimal_parabolic d)
    (V.subgroupOf (L ⊔ (T : Subgroup G))) d.reduced d.localActor hq d.localActor_kernel
    f.toLinearMap f.surjective (local_full_equivariant d hq) hk (local_thompson_moves d hJ)).2.2
  rw [←hV] at hs
  exact ReducedMarking.core_le_baumann_of_native_saturation L (T : Subgroup G)
    hb.2.1 T.isPGroup' d.normalizes_L R (map_subgroupOf_eq_of_le le_sup_right)
    (normal_extension_residual L (T : Subgroup G) d.twoPerfect T.isPGroup' d.normalizes_L) hs

theorem baumann_core_product_of_escape
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 =
      V ⊔ (baumann (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  have hSL : S ≤ normalizer (L : Set G) := inf_le_left.trans d.normalizes_L
  have hq := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ L ⊔ S from le_sup_left) (sup_le L.le_normalizer hSL)
  rw [hV] at hq
  have hQS : Q ≤ S := baumann_core_le_of_escape d hout
  have hc : Q ⊓ centralizer (L : Set G) = S ⊓ centralizer (L : Set G) := by
    apply le_antisymm (inf_le_inf_right _ hQS)
    apply le_inf ?_ inf_le_right
    have he := ReducedMarking.normal_short_extension_centralizer L S hb.2.1
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)) hSL
    apply le_trans ?_ he.le
    exact le_inf (inf_le_left.trans le_sup_right)
      (inf_le_right.trans (centralizer_le (map_subtype_le _)))
  exact hq.trans (congrArg (fun C => V ⊔ C) hc)

theorem exists_baumann_conjugate_core_escape
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ∃ g ∈ normalizer (baumann (T : Subgroup G) : Set G),
      g ∉ normalizer (L : Set G) ∧
      ¬V.map (MulAut.conj g⁻¹).toMonoidHom ≤ (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  let S := baumann (T : Subgroup G)
  have hSL : S ≤ normalizer (L : Set G) := inf_le_left.trans d.normalizes_L
  have hres : Stellmacher.twoResidualAmbient L = L := by
    rw [Stellmacher.twoResidualAmbient,twoResidualSubgroup_eq_pResidual,d.residual_eq_top,←MonoidHom.range_eq_map,range_subtype]
  have hU : ⁅L.pCoreIn 2,L⁆ = V := by
    rw [←hV]
    simp only [blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype,pCoreIn]
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hnorm : (S.subgroupOf (T : Subgroup G)).Normal :=
    normal_subgroupOf_of_le_normalizer hTS
  obtain ⟨g,hg,hgV⟩ := c6_3_exists_escaping_conjugate_local L S (T : Subgroup G) ⊤ hSL hres
    (baumann_core_le_of_escape d hout) (hU.symm ▸ d.chosen.ne_bot) inf_le_left hnorm
    (fun W hn hW hN => by
      simpa only [top_inf_eq] using baumann_normalizer_obstruction d hout W hn hW hN)
  have hgS : g ∈ normalizer (S : Set G) := by
    simpa only [top_inf_eq,sup_eq_left.mpr hTS] using hg
  change ¬⁅L.pCoreIn 2,L⁆.map (MulAut.conj g⁻¹).toMonoidHom ≤ (L ⊔ S).pCoreIn 2 at hgV
  rw [hU] at hgV
  refine ⟨g,hgS,?_,hgV⟩
  intro hgL
  have hnV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rw [←hV]
    exact normalizer_le_normalizer_characteristic_image L (blockU L)
  have he := mem_normalizer_iff_map_conj_eq.mp
    (hnV ((normalizer (L : Set G)).inv_mem hgL))
  apply hgV
  change V.map (↑(MulAut.conj g⁻¹)) ≤ (L ⊔ S).pCoreIn 2
  rw [he,baumann_core_product_of_escape d hout]
  exact le_sup_left

end CFSG.Quasithin.Chapter5.A5Source
