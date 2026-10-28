module

public import CFSG.Quasithin.Chapter13.Section02.A5Outside.Solvable
public import Theory.GroupTheory.ReducedNormal.SylowCenterSplitting
public import Theory.Representation.NormalElementaryQuotient.MovedGeneration

/-!
# Original 13.2.8(2): moved group and central seed

The actual solvable factor witness gives the residual fixed/moved direct
sum by odd-order averaging. On the literal omega-center orbit this fixed
summand is exactly C_Z(H), by the Sylow-center splitting theorem. We map
both summands back through the original inclusion H→G, obtaining the
printed identity U_H = [U_H,H] ⊕ C_Z(H).

No complement, factor identification or whole-centralizer equality is an
input. The genuine earlier 5.1.7(1) bound and 13.2.8(1) solvability are
retained, as in the accompanying factor and Baumann source consumer.
Source: Aschbacher–Smith 13.2.8(2), printed p.880; B.2.14, p.78.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual solvable action supplies the residual complement, then the full central splitting. -/
theorem solvable_omega_splitting (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (U : Subgroup G) (hU : IsPReduced 2 U)
    (hcl : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2) (hs : Group.IsSolvable G) :
    (⁅U,(⊤ : Subgroup G)⁆ : Subgroup G) ⊔
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ center G) = U ∧
      Disjoint (⁅U,(⊤ : Subgroup G)⁆ : Subgroup G)
        (omegaOneCenterAmbient (T : Subgroup G) ⊓ center G) := by
  let := hU.normal
  let := hU.elementary
  let := hs
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨d,_,_,_⟩ := ChapterE.ThompsonAction.source_solvable_factors
    T hP U hU hJ hrank inferInstance
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective
    U q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [QuotientGroup.ker_mk'] at he
    exact le_top.trans he.ge
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hne).2
  have hff : IsFFModule ρ := (isFFModule_iff_quadraticRatio_le_one ρ).mpr d.ratio_one.le
  have hr := (ChapterB.offender_generation (T.mapSurjective (QuotientGroup.mk'_surjective C))
    hp ρ hff hU.quotient_pCore_eq_bot).1
  let D := d.toSolvableFFFactors
  have hc := D.fixed_isCompl_moved hf hr
  have hgen : (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
      (U ⊓ centralizer (pResidual 2 G : Set G)) = U := by
    apply le_antisymm (sup_le (commutator_le_left _ _) inf_le_left)
    have hsum := hc.symm.sup_eq_top
    rw [← D.residual_moved_eq hf hr,← map_pResidual_of_surjective 2 q
      (QuotientGroup.mk'_surjective C)] at hsum
    have hrq : (pResidual 2 G).map q ≤ offenderSubgroup ρ := by
      rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective C)]
      exact hr
    exact NormalElementaryQuotient.le_commutator_sup_fixed_of_generation
      U q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (pResidual 2 G) (pResidual 2 G) U (offenderSubgroup ρ) hrq hrq hsum inf_le_left
  have hd : Disjoint (⁅U,pResidual 2 G⁆ : Subgroup G)
      (U ⊓ centralizer (pResidual 2 G : Set G)) := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro x ⟨hx,hxc⟩
    let v : Additive U := Additive.ofMul ⟨x,hxc.1⟩
    have hm : v ∈ subspaceCommutator ρ ⊤ (offenderSubgroup ρ) := by
      rw [← D.residual_moved_eq hf hr,← map_pResidual_of_surjective 2 q
        (QuotientGroup.mk'_surjective C),← NormalElementaryQuotient.commutatorSpace_eq
          U q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)]
      exact hx
    have hz : v ∈ fixedSpace ρ (offenderSubgroup ρ) := by
      rw [← D.fixed_residual_eq hf hr,← map_pResidual_of_surjective 2 q
        (QuotientGroup.mk'_surjective C)]
      exact (NormalElementaryQuotient.mem_fixedSpace_image U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) _ v).mpr hxc.2
    have hv := Submodule.disjoint_def.mp hc.disjoint v hz hm
    exact congrArg (fun a : Additive U => (a.toMul : G)) hv
  exact omegaCenter_span_splitting T U hcl
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) hgen hd

/-- The printed direct sum on the original ambient U_H, H and Z. -/
theorem source_omegaOrbit_splitting
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    (⁅omegaOrbit T H,H⁆ : Subgroup G) ⊔
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G)) = omegaOrbit T H ∧
      Disjoint (⁅omegaOrbit T H,H⁆ : Subgroup G)
        (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G)) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hUH : omegaOrbit T H ≤ H := conjugateSpanBy_le (hZT.trans hTH) H.le_normalizer
  let S := T.subtype hTH
  let U := (omegaOrbit T H).subgroupOf H
  have hzmap : (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hz : omegaOneCenterAmbient (S : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hzmap,map_subgroupOf_eq_of_le (hZT.trans hTH)]
  have hcl : U = normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H) := by
    rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ H (hZT.trans hTH)]
  obtain ⟨hsq,_,hp,hU,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  obtain ⟨hgen,hdis⟩ := solvable_omega_splitting S hp U hU hcl hj
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) hs
  have hfixed : (omegaOneCenterAmbient (S : Subgroup H) ⊓ center H).map H.subtype =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨hzmap ▸ mem_map_of_mem H.subtype hy.1,?_⟩
      intro h hh
      exact congrArg H.subtype (mem_center_iff.mp hy.2 ⟨h,hh⟩)
    · intro hx
      refine ⟨⟨x,hTH (hZT hx.1)⟩,⟨?_,mem_center_iff.mpr ?_⟩,rfl⟩
      · rw [hz]
        exact hx.1
      · intro h
        exact Subtype.ext (hx.2 h h.property)
  have hm : (⁅U,(⊤ : Subgroup H)⁆ : Subgroup H).map H.subtype = ⁅omegaOrbit T H,H⁆ := by
    rw [map_commutator,show U.map H.subtype = omegaOrbit T H from
      map_subgroupOf_eq_of_le hUH,← MonoidHom.range_eq_map,range_subtype]
  refine ⟨?_,?_⟩
  · have he := congrArg (map H.subtype) hgen
    rw [Subgroup.map_sup,hm,hfixed,map_subgroupOf_eq_of_le hUH] at he
    exact he
  · apply disjoint_iff.mpr
    have he := congrArg (map H.subtype) hdis.eq_bot
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,hm,hfixed,Subgroup.map_bot] at he
    exact he

end CFSG.Quasithin.Chapter13.Section02.A5Outside
