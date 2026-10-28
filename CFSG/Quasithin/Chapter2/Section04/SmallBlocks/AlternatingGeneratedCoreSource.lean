module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingWholeSquareActionSource
public import Theory.SpecificGroups.SymmetricFourWreath.CoreIndex
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CoreAction
/-!
# The two-core of the original generated local group

The full square-action image is O4+(2), whose two-core is trivial and whose
Sylow two-subgroups have order eight. The literal product E=P C_T(L) has
index eight in T. It is normal and a two-group, so it is exactly O2(KT).
The original maximal two-local group M contains KT; its two-core lies in T
and is normal in KT, hence lies in E as well.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_generated_core
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    let F := K ⊔ (T : Subgroup G)
    F.pCoreIn 2 = P ⊔ D ∧ M.pCoreIn 2 ≤ P ⊔ D := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let Di := centralizer (d.block : Set d.H)
  let E := P ⊔ D
  let F := K ⊔ (T : Subgroup G)
  have hDm : Di.map d.H.subtype=D :=
    d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 Di :=
    (d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA).2.2.1
  obtain ⟨e,he⟩ := d.single_alternating_marked_ambient_sylow_model hG T hM hTM hu hST hsingle hA
  have hDR : D≤R := by
    rw [show D=R⊓centralizer (d.block.map d.H.subtype : Set G) from
      d.single_block_sylow_centralizer T hST.le hsingle]
    exact inf_le_left
  obtain ⟨hPR,hRP⟩ := d.single_borel_core_placement hsingle
  have hER : E≤R := sup_le hPR hDR
  have hET : E≤(T : Subgroup G) := hER.trans hST.le
  let Q := P.subgroupOf R
  let eq : Q≃*P := subgroupOfEquivOfLe hPR
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hPR).mpr hRP
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let hq := hp.map eq.symm
  let : IsExtraspecial 2 Q := hq.extraspecial
  have hiR : E.relIndex R=4 := by
    have hh := SymmetricFourWreath.core_sup_factor_index e Q hq.card
    rw [he,hDm,←subgroupOf_sup hPR hDR] at hh
    exact hh
  have hiT : E.relIndex (T : Subgroup G)=8 := by
    have hh := relIndex_mul_relIndex E R (T : Subgroup G) hER hST.le
    rw [hiR,(d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1] at hh
    exact hh.symm
  obtain ⟨hD,hp',eE,hn,hfull⟩ := d.single_alternating_whole_square_action hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 D := hD
  have hEF : E≤F := hET.trans le_sup_right
  let : (E.subgroupOf F).Normal := (normal_subgroupOf_iff_le_normalizer hEF).mpr hn
  have hE2 : IsPGroup 2 (E.subgroupOf F) :=
    (T.isPGroup'.of_injective (inclusion hET) (inclusion_injective hET)).comap_subtype
  let f := (hp'.centralFactorWreathAction eE).comp (E.normalizerMonoidHom.comp (inclusion hn))
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp hfull
  have hF : F.pCoreIn 2=E := by
    have hh := BinaryFourPlus.twoCore_eq_of_surjective_sylow_index f hf
      (T.subtype (show (T : Subgroup G)≤F from le_sup_right)) (E.subgroupOf F) hE2
      (by rw [Sylow.coe_subtype,relIndex_subgroupOf (show (T : Subgroup G)≤F from le_sup_right)]; exact hiT)
    have hm := congrArg (map F.subtype) hh
    rwa [map_subgroupOf_eq_of_le hEF] at hm
  refine ⟨hF,?_⟩
  have hFM : F≤M := sup_le ((map_subtype_le _).trans inf_le_left) hTM
  have hPMT : M.pCoreIn 2≤(T : Subgroup G) := by
    have hh := pCoreIn_le_sylow M (T.subtype hTM)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] at hh
  have hPMF : M.pCoreIn 2≤F := hPMT.trans le_sup_right
  let : ((M.pCoreIn 2).subgroupOf F).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPMF).mpr
      (hFM.trans (M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  have hle : (M.pCoreIn 2).subgroupOf F≤pCore 2 F :=
    le_sSup ⟨inferInstance,(isPGroup_pCoreIn 2 M).comap_subtype⟩
  have hm := map_mono (f:=F.subtype) hle
  rw [map_subgroupOf_eq_of_le hPMF] at hm
  change M.pCoreIn 2≤F.pCoreIn 2 at hm
  exact hm.trans hF.le
end CFSG.Quasithin.Chapter2