module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceBlock
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Saturation
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Saturation
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section06.GeneralLocal
public import Stellmacher.SectionTwo.CubicSelectedQuotient

/-!
# The original A5 core and its escaping conjugate

The genuine five-point section saturates the centralizer of [W,L], putting
Q = O2(L Baum(T)) in Baum(T). The actual alternating block then gives
Q = [W,L] C_{Baum(T)}(L). The earlier local C.6.3 theorem supplies an
escaping conjugate of [W,L] under the full Baumann normalizer.

These constructions retain the original input and need no uniqueness over
L. That stronger uniqueness is still needed in the subsequent crossing
argument. Source: Aschbacher--Smith 5.1.7(1), p.633, using E.2.3 and C.6.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterC ChapterC.Section05.CounterexampleCharacteristic
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

/-- Saturation puts the original A5 core inside the original Baumann group. -/
theorem Input.baumann_core_le_of_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    (L ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 ≤
      ChapterB.baumann (T : Subgroup G) := by
  obtain ⟨_,hb,hV,_⟩ := h.alternating_block_of_baumann_escape hout
  let H := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf H
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let V := ⁅U,pResidual 2 H⁆
  let R := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hr : IsPReduced 2 V := h.reduced_internal.moved U
  have hVmap : V.map H.subtype = ⁅W,L⁆ := h.local_moved_map
  have hRmap : (R : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  obtain ⟨q,hq,hk,f,hf,he,hfk⟩ := h.five_section_of_baumann_escape hout
  change q.ker = centralizer (V : Set H) at hk
  have hfix : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation V q hq hk g v = v := by
    intro v hv g hg
    have hvf : v ∈ fixedSpace (NormalElementaryQuotient.representation V q hq hk)
        ((pResidual 2 H).map q) := hfk ▸ hv
    exact (mem_fixedSpace_iff _ _ v).mp hvf g
      ((ChapterC.SymmetricFive.source_residual_image q hq).symm ▸ hg)
  have hJR : ¬elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (V : Set H) := by
    intro hc
    apply hout
    let := h.quotient_quasisimple
    apply Chapter5.RankOneBaumannSource.baumann_normalizer_of_thompson_centralizes
      h.qtke h.maximal_local h.sylow_normalizes h.commutator_reduced.1
      h.commutator_input.reduced_internal h.quotient_center_eq_bot
      h.commutator_input.noncentral
    have hjm : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hRmap]
    rw [←hjm,←hVmap]
    rintro x ⟨x,hx,rfl⟩ v ⟨v,hv,rfl⟩
    exact congrArg H.subtype (hc hx v hv)
  have hs := (SymmetricFive.source_alpha_and_saturation R h.local_minimal_parabolic
    V hr q hq hk f hf he hfix hJR).2.2
  have hv : V = (⁅W,L⁆).subgroupOf H := by
    rw [←hVmap]
    exact (comap_map_eq_self_of_injective H.subtype_injective V).symm
  rw [hv,←hV] at hs
  exact ReducedMarking.core_le_baumann_of_native_saturation L (T : Subgroup G)
    hb.2.1 T.isPGroup' h.sylow_normalizes R hRmap h.local_residual_eq hs

/-- The literal core splits over the original moved module. -/
theorem Input.baumann_core_product_of_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    (L ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 =
      ⁅W,L⁆ ⊔ (ChapterB.baumann (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨_,hb,hV,_⟩ := h.alternating_block_of_baumann_escape hout
  let S := ChapterB.baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  have hSL : S ≤ normalizer (L : Set G) := inf_le_left.trans h.sylow_normalizes
  have hq := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ L ⊔ S from le_sup_left) (sup_le L.le_normalizer hSL)
  rw [hV] at hq
  have hQS : Q ≤ S := h.baumann_core_le_of_escape hout
  have hc : Q ⊓ centralizer (L : Set G) = S ⊓ centralizer (L : Set G) := by
    apply le_antisymm (inf_le_inf_right _ hQS)
    apply le_inf ?_ inf_le_right
    have he := ReducedMarking.normal_short_extension_centralizer L S hb.2.1
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)) hSL
    apply le_trans ?_ he.le
    exact le_inf (inf_le_left.trans le_sup_right)
      (inf_le_right.trans (centralizer_le (map_subtype_le _)))
  exact hq.trans (congrArg (fun C => ⁅W,L⁆ ⊔ C) hc)

/-- Source C.6.3 supplies an actual conjugator in N(Baum(T)), outside N(L),
whose original moved module escapes the original local core. -/
theorem Input.exists_baumann_conjugate_core_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ∃ g ∈ normalizer (ChapterB.baumann (T : Subgroup G) : Set G),
      g ∉ normalizer (L : Set G) ∧
      ¬(⁅W,L⁆ : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom ≤
        (L ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨_,_,hV,_⟩ := h.alternating_block_of_baumann_escape hout
  let S := ChapterB.baumann (T : Subgroup G)
  have hSL : S ≤ normalizer (L : Set G) := inf_le_left.trans h.sylow_normalizes
  have hres : Stellmacher.twoResidualAmbient L = L := by
    rw [Stellmacher.twoResidualAmbient,twoResidualSubgroup_eq_pResidual,
      (pResidual_eq_top_iff 2 L).mpr h.local_mem.2.2.1,
      ←MonoidHom.range_eq_map,range_subtype]
  have hU : ⁅L.pCoreIn 2,L⁆ = ⁅W,L⁆ := by
    rw [←hV]
    simp only [blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype,pCoreIn]
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hnorm : (S.subgroupOf (T : Subgroup G)).Normal :=
    normal_subgroupOf_of_le_normalizer hTS
  obtain ⟨g,hg,hgV⟩ := c6_3_exists_escaping_conjugate_local L S (T : Subgroup G) ⊤ hSL hres
    (h.baumann_core_le_of_escape hout) (hU.symm ▸ h.noncentral) inf_le_left hnorm
    (fun A hn hA hN => by
      have hh := Chapter5.RankOneBaumannSource.normalizer_obstruction_of_baumann_escape
        h.qtke h.maximal_local h.sylow_normalizes hout A hn hA
        ((normal_subgroupOf_iff_le_normalizer (hA.trans (inf_le_left.trans le_sup_right))).mp hN)
      simpa only [top_inf_eq] using hh)
  have hgS : g ∈ normalizer (S : Set G) := by
    simpa only [top_inf_eq,sup_eq_left.mpr hTS] using hg
  change ¬⁅L.pCoreIn 2,L⁆.map (MulAut.conj g⁻¹).toMonoidHom ≤ (L ⊔ S).pCoreIn 2 at hgV
  rw [hU] at hgV
  refine ⟨g,hgS,?_,hgV⟩
  intro hgL
  have hnV : normalizer (L : Set G) ≤ normalizer ((⁅W,L⁆ : Subgroup G) : Set G) := by
    rw [←hV]
    exact normalizer_le_normalizer_characteristic_image L (blockU L)
  have he := mem_normalizer_iff_map_conj_eq.mp
    (hnV ((normalizer (L : Set G)).inv_mem hgL))
  apply hgV
  change (⁅W,L⁆ : Subgroup G).map (↑(MulAut.conj g⁻¹)) ≤ (L ⊔ S).pCoreIn 2
  rw [he,h.baumann_core_product_of_escape hout]
  exact le_sup_left

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
