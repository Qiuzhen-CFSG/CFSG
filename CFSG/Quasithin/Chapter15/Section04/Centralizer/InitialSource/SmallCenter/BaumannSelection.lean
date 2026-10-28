module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.BaumannKernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.SelectedSylow
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.SelectedModule
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# Constructing the original selected Baumann local-class member

The native solvable selected-coordinate theorem supplies an actual K with
Baumann Sylow, nested SL₂(2) quotient, and a four-group moved by its cubic
residual. The original omega-center centralizer identity makes the literal
local kernel O₂(K). Cubic residual transport computes F* of that quotient,
and the original commutator sandwich constructs the exact natural module.
Thus K belongs to C.1.17; membership and its action are proved outputs.

The original normal closure of the Baumann group supplies characteristic two
for K. Its selected Sylow and the nested quotient supply minimal parabolicity.
All source maps remain inclusions and the given centralizer quotient map.
Source: Aschbacher--Smith C.1.26 and 15.4.7, printed pp.132 and1158;
Stellmacher (2.4), used in the opening paragraph of (6.3).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open ChapterC.GlaubermanNiles SectionTwo
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A genuine local-class member, constructed from the original source geometry. -/
theorem exists_baumann_localClass
    (h : SectionTwo.Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ centralizer (SectionTwo.vSubgroup S : Set G))
    (hnot : ¬ SectionTwo.vSubgroup S ≤ centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G))
    (hu : IsUniqueMaximalContaining (S : Subgroup G) ⊤)
    (hC : centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) = S) :
    ∃ (K : Subgroup G) (hBK : ChapterB.baumann (S : Subgroup G) ≤ K),
      InLocalClass (inclusion hBK) ∧ K ⊔ (S : Subgroup G) = ⊤ := by
  classical
  let B := (S : Subgroup G) ⊓ centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
  let L := normalClosure (B : Set G)
  let Z := normalClosure (omegaOneCenterAmbient B : Set G)
  let : L.Normal := normalClosure_normal
  let : Z.Normal := normalClosure_normal
  obtain ⟨PB,hPB,hL,_,_,_,hVL,hVZ,_,_⟩ :=
    baumann_omega_supplement_data h S hcore hnot hu
  change (PB : Subgroup L).map L.subtype = B at hPB
  have hseedZ : omegaOneCenterAmbient (S : Subgroup G) ≤ Z :=
    (show omegaOneCenterAmbient (S : Subgroup G) ≤ SectionTwo.vSubgroup S from
      le_normalClosure).trans (hVZ.trans_eq hVL)
  let q := QuotientGroup.mk' (centralizer (Z : Set G))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (Z : Set G) := QuotientGroup.ker_mk' _
  have hkp : IsPGroup 2 q.ker := by
    apply S.isPGroup'.to_le
    rw [hk]
    exact (centralizer_le hseedZ).trans_eq hC
  obtain ⟨hZe,_,_,n,D,K,P,i,_,_,hDF,_,_,hBK,hKL,hP,hSL,hgen,_,hR,hW,hfour,_,_⟩ :=
    baumann_omega_selected_module h S hcore hnot hu B L Z rfl rfl rfl q hq hk
  have hfit : generalizedFitting K = pCore 2 K := by
    have hPBK : (PB : Subgroup L) ≤ K.subgroupOf L := by
      intro x hx
      exact hBK (hPB ▸ mem_map_of_mem L.subtype hx)
    have hc := centralizer_pCore_le_of_pCore_le (K.subgroupOf L)
      hL.centralizer_twoCore_le ((pCore_isPGroup.le_sylow_of_normal PB).trans hPBK)
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hKL)).mp hc)
  have hkernel : localKernel (inclusion hBK) = pCore 2 K :=
    selected_localKernel S K P hP hC
  have hRcard : Nat.card ((pResidual 2 K).map (q.comp K.subtype)) = 3 := by
    rw [←map_map,←twoResidualSubgroup_eq_pResidual K]
    change Nat.card ((twoResidualAmbient K).map q) = 3
    rw [hR,card_map_of_injective (L.map q).subtype_injective,
      card_map_of_injective (D i).subtype_injective]
    exact isSL2Two_commutator_card (hDF i).1
  have hcoreR := residual_pCoreQuotient_card_of_cubic_image (q.comp K.subtype)
    hkp.comap_subtype hRcard (SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hSL)
  have hstarR : Nat.card (pResidual 2 (LocalStar (inclusion hBK))) = 3 := by
    let a := QuotientGroup.quotientMulEquivOfEq hkernel
    have hm := map_pResidual_of_surjective 2 a.toMonoidHom a.surjective
    calc
      _ = Nat.card ((pResidual 2 (LocalStar (inclusion hBK))).map a.toMonoidHom) :=
        (card_map_of_injective a.injective).symm
      _ = Nat.card (pResidual 2 (K ⧸ pCore 2 K)) := by rw [hm]
      _ = 3 := hcoreR
  let : IsElementaryAbelian 2 Z := hZe
  let : IsElementaryAbelian 2 (localV (inclusion hBK)) :=
    selected_localV_elementary B K Z hBK le_normalClosure
  refine ⟨K,hBK,?_,hgen⟩
  refine inLocalClass_of_cubic_residual (inclusion hBK) (inclusion_injective hBK)
      ?_ hfit hkernel hstarR ?_
  · refine ⟨P,?_,minimalParabolic_of_nested_sl2 P hSL⟩
    apply map_injective K.subtype_injective
    rw [MonoidHom.range_eq_map, map_map,hP]
    change (⊤ : Subgroup B).map B.subtype = B
    rw [←MonoidHom.range_eq_map,range_subtype]
  · exact selected_localV_residual_card B K Z hBK le_normalClosure hW hfour
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
