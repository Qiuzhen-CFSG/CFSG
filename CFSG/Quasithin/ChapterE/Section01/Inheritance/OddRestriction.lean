module
public import CFSG.Quasithin.ChapterE.Section01.Inheritance.IntrinsicTransport
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Restricting an odd E-member without changing its actor

An intermediate subgroup containing the original actor and the full
embedded two-residual retains E1. Its image in the original two-core
quotient contains the same normal odd core. Restricting the original
quotient map has a two-group kernel, so the full commutator condition and
the actor's exact quotient rank one survive in the intrinsic new quotient.
No normality of the intermediate subgroup is required.

This is the odd local branch of the changed-Sylow generation step in
Aschbacher--Smith 6.1.4, printed p.665, using E.1.2(E1), pp.209--210.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem odd_core_residual {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hq : IsPGroup 2 (G ⧸ pCore p G)) : pResidual 2 G = pCore p G := by
  refine le_antisymm (sInf_le ⟨inferInstance,hq⟩) ?_
  apply le_sInf
  rintro N ⟨hN,hQ⟩
  let := hN
  let q := QuotientGroup.mk' N
  have hz : (pCore p G).map q = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne p 2 hp _ _ (pCore_isPGroup.map q) (hQ.to_subgroup _))
  simpa only [q,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] using hz

private theorem odd_restriction (A C : Subgroup G) (hAC : A ≤ C)
    (hRC : pResidual 2 G ≤ C)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hquot : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ pCore p (G ⧸ pCore 2 G)))
    (hne : pCore p (G ⧸ pCore 2 G) ≠ ⊥)
    (hcomm : pCore p (G ⧸ pCore 2 G) =
      ⁅pCore p (G ⧸ pCore 2 G),A.map (QuotientGroup.mk' (pCore 2 G))⁆)
    (hrank : Group.rank (A.map (QuotientGroup.mk' (pCore 2 G))) = 1) :
    ECaseOdd A C := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  let q := QuotientGroup.mk' (pCore 2 G)
  let P := pCore p (G ⧸ pCore 2 G)
  let H := C.map q
  let f : C →* H := q.subgroupMap C
  have hres : (pResidual 2 G).map q = P := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    exact odd_core_residual hp2 hquot
  have hPH : P ≤ H := hres ▸ map_mono (f := q) hRC
  let N := P.subgroupOf H
  have hNmap : N.map H.subtype = P := map_subgroupOf_eq_of_le hPH
  have hker : f.ker = (pCore 2 G).subgroupOf C := by
    ext x
    change (f x = 1) ↔ (x : G) ∈ pCore 2 G
    rw [←Subtype.val_inj]
    exact QuotientGroup.eq_one_iff (x : G)
  have hk : IsPGroup 2 f.ker := hker ▸ pCore_isPGroup.comap_subtype
  have hAmap : ((A.subgroupOf C).map f).map H.subtype = A.map q := by
    rw [map_map]
    change (A.subgroupOf C).map (q.comp C.subtype) = A.map q
    rw [←map_map,map_subgroupOf_eq_of_le hAC]
  have hNquot : IsPGroup 2 (H ⧸ N) := by
    let g := (QuotientGroup.mk' P).comp H.subtype
    have hNg : N = g.ker := by
      ext x
      exact (QuotientGroup.eq_one_iff (N := P) (x : G ⧸ pCore 2 G)).symm
    exact (hquot.to_subgroup g.range).of_equiv
      ((QuotientGroup.quotientKerEquivRange g).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hNg.symm))
  have hNne : N ≠ ⊥ := by
    intro hz
    apply hne
    change P = ⊥
    rw [←hNmap,hz,Subgroup.map_bot]
  have hNc : N = ⁅N,(A.subgroupOf C).map f⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,hNmap,hAmap]
    exact hcomm
  have hAr : Group.rank ((A.subgroupOf C).map f) = 1 := by
    rw [←hrank]
    exact Group.rank_congr
      ((((A.subgroupOf C).map f).equivMapOfInjective H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr hAmap))
  exact ⟨p,hp,ho,odd_quotient_commutator_rank_of_surjective hp2 f
    (q.subgroupMap_surjective C) hk N (A.subgroupOf C)
    pCore_isPGroup.comap_subtype hNquot hNne hNc hAr⟩

/-- E1 survives restriction to any subgroup containing the same actor and
the original embedded two-residual. Its intrinsic actor rank is still one. -/
theorem ECaseOdd.restrict_of_residual_le {A K C : Subgroup G}
    (h : ECaseOdd A K) (hCK : C ≤ K) (hAC : A ≤ C)
    (hRC : (pResidual 2 K).map K.subtype ≤ C) : ECaseOdd A C := by
  obtain ⟨p,hp,ho,hquot,hne,hcomm,hrank⟩ := h
  have hres : pResidual 2 K ≤ C.subgroupOf K := map_le_iff_le_comap.mp hRC
  have hc := odd_restriction (A.subgroupOf K) (C.subgroupOf K)
    (subgroupOf_mono K hAC) hres hp ho hquot hne hcomm hrank
  have hm := hc.map_injective K.subtype K.subtype_injective
  rwa [map_subgroupOf_eq_of_le hCK,map_subgroupOf_eq_of_le (hAC.trans hCK)] at hm

end CFSG.Quasithin.ChapterE
