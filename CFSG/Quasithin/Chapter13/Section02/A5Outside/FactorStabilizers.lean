module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.BaumannGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.FactorNormalizers
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WholeActor

/-!
# Stabilizers of the original outside-group factors

The actual E.2.3 representation supplies two S₃ factors. Their normalizer
in the faithful action is the product layer, so their full preimages in H
have Sylow normalizer equal to the preimage of the layer inside T. The
original Baumann image is that Sylow intersection, and its full kernel
O₂(H) is already in Baum(T). Thus N_T(Hᵢ)=Baum(T) for both original Hᵢ.

These are the literal preimages under H→H/C_H(U_H), mapped by H→G.
No replacement factors, split extension, or block assertion is assumed.
The final theorem applies the result to H∨O²(N_L(T∩L)) having trivial
two-core. Together with BaumannGeometry this supplies the factor-normalizer,
point-centralizer and core-product pieces of13.2.11(4); the factor fixed-line
marking and the nonblock arguments remain separate source steps.
Source: Aschbacher–Smith 13.2.8(3) and13.2.11(4), pp.880–882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

theorem source_solvable_paired_factor_normalizers
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      ∀ i, (T : Subgroup G) ⊓ normalizer (((c.factor i).comap q).map H.subtype : Set G) =
        ChapterB.baumann (T : Subgroup G) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,hc,ht⟩ := source_solvable_paired_factors d hH hB hZ hs hz
  let D := c.toSolvableFFFactors
  obtain ⟨_,_,hp,_,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective
    U q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hj
    rw [QuotientGroup.ker_mk'] at he
    exact le_top.trans he.ge
  have hpq := (ChapterB.minimalParabolic_reduced_image S hp q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hne).2
  have hff : IsFFModule ρ := (isFFModule_iff_quadraticRatio_le_one ρ).mpr c.ratio_one.le
  have hr := (ChapterB.offender_generation (S.mapSurjective (QuotientGroup.mk'_surjective C))
    hpq ρ hff hU.quotient_pCore_eq_bot).1
  have hcent := D.centralizer_eq_bot_of_residual hf hU.quotient_pCore_eq_bot hr
  have hBq := (ChapterE.ThompsonAction.solvable_pair_images_of_factors S hp U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hU.quotient_pCore_eq_bot (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
    hj c hc ht).2
  have hSm : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hBm : (ChapterB.baumann (S : Subgroup H)).map H.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    change ((S : Subgroup H) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H)).map H.subtype = _
    rw [baumann_map_injective H.subtype H.subtype_injective,hSm]
    rfl
  have hkB : q.ker ≤ ChapterB.baumann (S : Subgroup H) := by
    have hO := sup_eq_right.mp (source_core_products_eq_baumann d hH hB hZ hs hz).2
    have hC : C = pCore 2 H := source_omega_centralizer_eq_twoCore d hH hB hZ hs
    intro x hx
    rw [QuotientGroup.ker_mk',hC] at hx
    have hxG := hO (mem_map_of_mem H.subtype hx)
    rw [← hBm] at hxG
    obtain ⟨b,hb,he⟩ := hxG
    exact (H.subtype_injective he) ▸ hb
  have hlocal (i : Fin c.count) :
      (S : Subgroup H) ⊓ normalizer ((c.factor i).comap q : Set H) =
        ChapterB.baumann (S : Subgroup H) := by
    have hn : normalizer ((c.factor i).comap q : Set H) = (offenderSubgroup ρ).comap q := by
      rw [← comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective C),
        D.factor_normalizer_eq_of_two hc hcent]
    rw [hn]
    apply le_antisymm
    · intro x hx
      have hqx : q x ∈ (ChapterB.baumann (S : Subgroup H)).map q := by
        rw [hBq]
        exact ⟨mem_map_of_mem q hx.1,hx.2⟩
      obtain ⟨b,hb,hbq⟩ := hqx
      have hxk : x * b⁻¹ ∈ q.ker := by
        rw [MonoidHom.mem_ker,map_mul,map_inv,hbq,mul_inv_cancel]
      have hh := (ChapterB.baumann (S : Subgroup H)).mul_mem (hkB hxk) hb
      simpa only [inv_mul_cancel_right] using hh
    · refine le_inf inf_le_left ?_
      intro x hx
      exact (hBq ▸ mem_map_of_mem q hx).2
  refine ⟨c,hc,ht,?_⟩
  intro i
  have hnorm : (normalizer (((c.factor i).comap q).map H.subtype : Set G)).comap H.subtype =
      normalizer ((c.factor i).comap q : Set H) := by
    have hrng : ((c.factor i).comap q).map H.subtype ≤ H.subtype.range :=
      (map_subtype_le _).trans_eq H.range_subtype.symm
    rw [comap_normalizer_eq_of_le_range hrng,comap_map_eq_self_of_injective H.subtype_injective]
  have hmap : ((S : Subgroup H) ⊓ normalizer ((c.factor i).comap q : Set H)).map H.subtype =
      (T : Subgroup G) ⊓ normalizer (((c.factor i).comap q).map H.subtype : Set G) := by
    rw [← hnorm]
    ext x
    constructor
    · rintro ⟨y,⟨hyS,hyN⟩,rfl⟩
      exact ⟨hSm ▸ mem_map_of_mem H.subtype hyS,hyN⟩
    · intro hx
      obtain ⟨y,hyS,rfl⟩ := hSm.ge hx.1
      exact ⟨y,⟨hyS,hx.2⟩,rfl⟩
  rw [← hmap,hlocal,hBm]
theorem source_coreFree_borel_join_factor_normalizers
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      ∀ i, (T : Subgroup G) ⊓ normalizer (((c.factor i).comap q).map H.subtype : Set G) =
        ChapterB.baumann (T : Subgroup G) :=
  source_solvable_paired_factor_normalizers d hH hB hZ hs
    (source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore)

end CFSG.Quasithin.Chapter13.Section02.A5Outside
