module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.CoreProduct
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.ConjugateImages
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.ConjugateEscape
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The direct core product on the original embedded subgroups

Restrict V and its moving conjugate to Y = LB and use the prescribed
quotient of Y by O₂(Y). The short component identifies the full core
commutator with V. The literal conjugate centralizer has index eight,
so the two-root-eight index theorem splits O₂(Y) over C_B(L). The same
conjugate centralizes that entire factor. All normality is relative to Y.

Source: Aschbacher--Smith 13.3.10(2), printed p.888. The original flag
application is OriginalUnitaryNoncentrality.CoreProduct.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

theorem unitary_baumann_conjugate_core_product
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : ChosenModule T L V) (hshort : ChapterC.IsShort L)
    (B : Subgroup G) (hVB : V ≤ B) (hBL : B ≤ normalizer (L : Set G))
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (hn : L ⊔ B ≤ normalizer (V : Set G))
    (eY : ((L ⊔ B : Subgroup G) ⧸ pCore 2 (L ⊔ B : Subgroup G)) ≃* Atlas.G2.Model F)
    (heY : ∀ y : (L ⊔ B : Subgroup G), eY (QuotientGroup.mk' (pCore 2 (L ⊔ B : Subgroup G)) y) =
      rho (V.normalizerMonoidHom.rangeRestrict ⟨y,hn y.property⟩))
    (hcore : (L ⊔ B).pCoreIn 2 = B ⊓ centralizer (V : Set G))
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (x : G) (hx : x ∈ normalizer (B : Set G))
    (himage : (inducedAutomizer V (V.map (MulAut.conj x⁻¹).toMonoidHom)).map rho =
      Atlas.G2.BinaryCore.elementary)
    (hindex : ((L ⊔ B).pCoreIn 2).relIndex B = 8) :
    let Q := (L ⊔ B).pCoreIn 2
    let C := B ⊓ centralizer (L : Set G)
    Q = V ⊔ C ∧ Disjoint V C ∧ C ≤ centralizer (V.map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  intro Q C
  let Y := L ⊔ B
  let U := V.subgroupOf Y
  let K := L.subgroupOf Y
  let A := V.map (MulAut.conj x⁻¹).toMonoidHom
  let A' := A.subgroupOf Y
  have hVY : V ≤ Y := hVB.trans le_sup_right
  have hBa : B.map (MulAut.conj x⁻¹).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hx)
  have hAB : A ≤ B := (map_mono hVB).trans_eq hBa
  have hAY : A ≤ Y := hAB.trans le_sup_right
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hBL)
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let q : Y →* Atlas.G2.Model F := eY.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))
  have hq : Function.Surjective q := eY.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 Y := by
    ext y
    change eY (QuotientGroup.mk' (pCore 2 Y) y) = 1 ↔ _
    rw [←eY.map_one,eY.injective.eq_iff]
    exact QuotientGroup.eq_one_iff y
  have hmapA : A'.map q = Atlas.G2.BinaryCore.elementary := by
    rw [←himage]
    ext a
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨_,⟨⟨y,hn y.property⟩,hy,rfl⟩,(heY y).symm⟩
    · rintro ⟨_,⟨n,hnA,rfl⟩,rfl⟩
      exact ⟨⟨n.val,hAY hnA⟩,hnA,heY ⟨n.val,hAY hnA⟩⟩
  have hVC : V ≤ centralizer (V : Set G) := le_centralizer V
  have hVQ : V ≤ Q := (le_inf hVB hVC).trans hcore.ge
  have hUQ : U ≤ pCore 2 Y := by
    intro u hu
    have hh := hVQ hu
    obtain ⟨z,hz,heq⟩ := hh
    exact (Subtype.ext heq : z = u) ▸ hz
  have hcent : U ≤ centralizer (pCore 2 Y : Set Y) := by
    intro u hu z hz
    apply Subtype.ext
    exact ((le_centralizer_iff.mp (hcore.le.trans inf_le_right)) hu) z
      (mem_map_of_mem Y.subtype hz)
  have hUeq : (ChapterC.blockU K).map K.subtype = U := by
    apply map_injective Y.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hVY]
    have hcomp : Y.subtype.comp K.subtype = L.subtype.comp eK.toMonoidHom := rfl
    rw [hcomp,←map_map,ChapterC.blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective _ eK.surjective]
    exact (RecognitionSource.FusionReducibleNormalizer.chosen_eq_blockU chosen hshort).symm
  have hcomm : ⁅pCore 2 Y,K⁆ ≤ U := by
    rw [←hUeq]
    exact commutator_le_core_commutator_of_isSubnormal K (pCore 2 Y)
      (inferInstance : K.Normal).isSubnormal (hshort.of_mulEquiv eK.symm).twoPerfect
      pCore_isPGroup le_normalizer_of_normal
  have hfixU : U ⊓ centralizer (K : Set Y) = ⊥ := by
    apply le_bot_iff.mp
    rintro u ⟨hu,huc⟩
    apply Subtype.ext
    apply hfix.le
    refine ⟨hu,?_⟩
    intro l hl
    exact congrArg Subtype.val (huc ⟨l,(show L ≤ Y from le_sup_left) hl⟩ hl)
  have hcard : Nat.card U = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVY).toEquiv,
      Nat.card_congr Additive.ofMul, Nat.card_congr E.toEquiv]
    change Nat.card (Fin 6 → ZMod 2) = 64
    norm_num [Nat.card_fun]
  have hidxA : (centralizer (A : Set G)).relIndex B = 8 := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (centralizer (V : Set G)) B (MulAut.conj x⁻¹).injective
    rw [Theory.GroupTheory.map_centralizer_equiv,hBa] at hh
    rw [hcore,inf_relIndex_left] at hindex
    exact hh.trans hindex
  have hcentA : centralizer (A' : Set Y) = (centralizer (A : Set G)).subgroupOf Y := by
    ext y
    constructor
    · intro hh a ha
      exact congrArg Subtype.val (hh ⟨a,hAY ha⟩ ha)
    · intro hh a ha
      exact Subtype.ext (hh a ha)
  have hi : (centralizer (A' : Set Y)).relIndex (pCore 2 Y) ≤ 8 := by
    rw [hcentA,subgroupOf,relIndex_comap]
    exact (relIndex_le_of_le_right (hcore.le.trans inf_le_left)
      (index_ne_zero_of_finite)).trans hidxA.le
  obtain ⟨hs,hd,hc⟩ := unitary_core_product_of_moving_eight (pCore 2 Y) U K A'
    q hq hk hmapA hUQ hcent hcomm hfixU hcard hi
  have hfixed : (pCore 2 Y ⊓ centralizer (K : Set Y)).map Y.subtype = C := by
    rw [map_inf _ _ _ Y.subtype_injective,map_centralizer_subtype,
      map_subgroupOf_eq_of_le (show L ≤ Y from le_sup_left)]
    change Q ⊓ (Y ⊓ centralizer (L : Set G)) = C
    have hCQ : C ≤ Q := (le_inf inf_le_left
      (inf_le_right.trans (centralizer_le chosen.le_component))).trans hcore.ge
    apply le_antisymm
    · exact le_inf (inf_le_left.trans (hcore.le.trans inf_le_left)) (inf_le_right.trans inf_le_right)
    · exact le_inf hCQ (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  have hs' := congrArg (map Y.subtype) hs
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVY,hfixed] at hs'
  refine ⟨hs',?_,?_⟩
  · have hh := congrArg (map Y.subtype) hd.eq_bot
    rw [map_inf _ _ _ Y.subtype_injective,map_subgroupOf_eq_of_le hVY,hfixed,Subgroup.map_bot] at hh
    exact disjoint_iff.mpr hh
  · have hh := map_mono (f := Y.subtype) hc
    rw [hfixed,map_centralizer_subtype,map_subgroupOf_eq_of_le hAY] at hh
    exact hh.trans inf_le_right
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
