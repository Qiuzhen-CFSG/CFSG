module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Baumann
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedBlockSteps
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.FactorMarking
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# The actual selected A5 component and its normalizing Sylow

Select the solvable residual of the same marked alternating-axis preimage.
The original Baumann image normalizes it. Subnormal Sylow restriction then
constructs the prescribed Sylow in its join with the original Sylow normalizer;
characteristic two is inherited from the original source group.

Source: Aschbacher–Smith C.1.23–28, pp.129–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction Chapter1.Section02
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
/-- The whole paired actor normalizes its marked alternating first axis. -/
theorem five_first_axis_normalized
    (Y : Subgroup H) (e : Y ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) :
    Y ≤ normalizer ((alternatingGroup (Fin 5)).map
      (SymmetricFive.Paired.leftFactorMap Y e) : Set H) := by
  let j := SymmetricFive.Paired.leftFactorMap Y e
  let A := (alternatingGroup (Fin 5)).map j
  let Q : Subgroup (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) := (alternatingGroup (Fin 5)).prod ⊥
  let D := Q.map e.symm.toMonoidHom
  let : D.Normal := Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
  have ha : A = D.map Y.subtype := by
    ext x
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨e.symm (g,1),⟨(g,1),⟨hg,one_mem _⟩,rfl⟩,rfl⟩
    · rintro ⟨g,⟨z,hz,rfl⟩,rfl⟩
      refine ⟨z.1,hz.1,?_⟩
      change ((e.symm (z.1,1):Y):H) = ((e.symm z:Y):H)
      exact congrArg (fun z => ((e.symm z:Y):H)) (Prod.ext rfl hz.2.symm)
  change Y ≤ normalizer (A : Set H)
  rw [ha]
  have hh := D.le_normalizer_map Y.subtype
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh

/-- The selected A5 component has an actual normalizing Sylow supplement. -/
theorem first_five_component_geometry
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
    let A := (alternatingGroup (Fin 5)).map (SymmetricFive.Paired.leftFactorMap Y c.action.groupEquiv)
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = A ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      (solvableResidual (A.comap q)).map (A.comap q).subtype = L ∧
      U ≤ normalizer (L : Set G) ∧ baumann (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      (let N := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
       generalizedFitting N = pCore 2 N ∧
       ∃ R : Sylow 2 N, (R : Subgroup N).map N.subtype = (T : Subgroup G) ⊓ normalizer (L : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let e := c.action.groupEquiv
  let j := SymmetricFive.Paired.leftFactorMap Y e
  let A := (alternatingGroup (Fin 5)).map j
  let := offenderSubgroup_normal α
  have hA : IsComponent H A := SymmetricFive.Paired.leftFactorMap_component Y e
  let eA : A ≃* alternatingGroup (Fin 5) :=
    ((alternatingGroup (Fin 5)).equivMapOfInjective j (SymmetricFive.Paired.leftFactorMap_injective Y e)).symm
  obtain ⟨L,hL,him,heL,hcan,hnorm⟩ := exists_five_component_of_reduced_module
    h36 hG T hP U hU hJ q hq hk hs A hA eA
  have hYA : Y ≤ normalizer (A : Set H) := five_first_axis_normalized Y e
  have hUL : U ≤ normalizer (L : Set G) := hnorm U (by
    have hu : U ≤ q.ker := hk ▸ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    rw [(Subgroup.map_eq_bot_iff (H := U) (f := q)).mpr hu]
    exact bot_le)
  obtain ⟨hJB,a,b,hB⟩ := SymmetricFive.Paired.thompson_baumann_of_source_model
    T hP U hU hJ q hq hk d c hexchange
  have hBY : (baumann (T : Subgroup G)).map q ≤ Y := by
    rw [hB]
    exact (map_le_range _ _).trans (by
      rintro x ⟨z,rfl⟩; exact (e.symm z).property)
  have hBL := hnorm (baumann (T : Subgroup G)) (hBY.trans hYA)
  let R₀ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let N := L ⊔ R₀
  have hR : IsPGroup 2 R₀ := T.isPGroup'.to_le inf_le_left
  have hf : generalizedFitting N = pCore 2 N := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact centralizer_pCore_sup_le 2 L R₀
      (subnormal_core_selfCentralizing ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit) L hL.subnormal)
      hR inf_le_right
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  obtain ⟨R,hR⟩ := hR.exists_sylow_sup_of_coprime_index L R₀ inf_le_right
    (S : Subgroup L) S.not_dvd_index (by
      rintro x ⟨s,hs,rfl⟩
      refine ⟨?_,L.le_normalizer s.property⟩
      change s ∈ (T : Subgroup G).subgroupOf L
      rwa [←hS])
  exact ⟨L,hL,him,heL,hcan,hUL,hBL,hf,R,hR⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
