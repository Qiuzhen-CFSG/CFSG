module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointProduct
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.Intrinsic
public import CFSG.Quasithin.ChapterC.Section03.A5.FullSylowExclusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# The deleted-five core and the Hermitian positive-closure exclusion

In the literal quotient C_G(z)/O₂(C_G(z)), the image of L_z has two-core
V/V_z because O₂(L_z) = O₂(C_G(z))V. The exact quotient maps transport the
five-point A₅ action to that entire core. The intrinsic block constructor
then establishes every deleted-five block clause, including the original
action, without assuming a block or a splitting.

The full source SQTK catalogue gives a containing quasisimple component.
Restriction of the original Sylow and local component allows the proved
full-Sylow deleted-five exclusion to apply. The Chapter 12 consumer derives
all premises from the same original positive-closure Hermitian tensor.
Source: Aschbacher–Smith 8.2.13(1), printed pp.722–723, refs/quasithin.pdf,
using A.3.12–14 and the actual five-point module from 8.2.11(3).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  by_contra hn
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent

private theorem block_of_full_core_image
    {H : Type*} [Group H] [Finite H]
    (V R : Subgroup G) (hVR : V ≤ R) (hRV : R ≤ normalizer (V : Set G))
    [Group.IsPerfect R]
    (f : R →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1))
    (g : V →* pCore 2 H) (hg : Function.Surjective g)
    (hgval : ∀ v, (g v : H) = f (inclusion hVR v))
    (q : V →* Multiplicative (BinaryPermutation.core (Fin 5)))
    (hq : Function.Surjective q) (hker : g.ker = q.ker)
    (hact : ∀ (r : R) (v : V),
      (q (V.normalizerMonoidHom (inclusion hRV r) v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 5)
          (OrthogonalFourMinus.FivePoint.Construction.comparison.groupEquiv
            (eR (QuotientGroup.mk' (pCore 2 R) r))).val (q v).toAdd) :
    ChapterC.IsAlternatingBlock H 5 := by
  let eV : pCore 2 H ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    (QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  have heV (v : V) : eV (g v) = q v := by
    change (QuotientGroup.quotientKerEquivOfSurjective q hq)
      ((QuotientGroup.quotientMulEquivOfEq hker)
        ((QuotientGroup.quotientKerEquivOfSurjective g hg).symm (g v))) = q v
    rw [show (g v) = (QuotientGroup.quotientKerEquivOfSurjective g hg)
      (QuotientGroup.mk' g.ker v) from rfl, MulEquiv.symm_apply_apply]
    rfl
  let eQ := ((f.pCoreQuotientEquiv hf hk).symm.trans eR).trans
    OrthogonalFourMinus.FivePoint.Construction.comparison.groupEquiv
  have heQ (r : R) : eQ (QuotientGroup.mk' (pCore 2 H) (f r)) =
      OrthogonalFourMinus.FivePoint.Construction.comparison.groupEquiv
        (eR (QuotientGroup.mk' (pCore 2 R) r)) := by
    change OrthogonalFourMinus.FivePoint.Construction.comparison.groupEquiv
      (eR ((f.pCoreQuotientEquiv hf hk).symm
        (QuotientGroup.mk' (pCore 2 H) (f r)))) = _
    rw [←MonoidHom.pCoreQuotientEquiv_apply f hf hk, MulEquiv.symm_apply_apply]
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective hf
  apply ChapterC.AlternatingFiveIntrinsic.alternatingBlock eQ eV ?_ perfect_twoPerfect
  intro a b
  obtain ⟨r,rfl⟩ := hf a
  obtain ⟨v,rfl⟩ := hg b
  have hgconj : MulAut.conjNormal (f r) (g v) =
      g (V.normalizerMonoidHom (inclusion hRV r) v) := by
    apply Subtype.ext
    change f r*(g v : H)*(f r)⁻¹ = _
    rw [hgval,hgval]
    change f r*f (inclusion hVR v)*(f r)⁻¹ =
      f (r*(inclusion hVR v)*r⁻¹)
    simp only [map_mul,map_inv]
  rw [hgconj,heV,heV,heQ]
  exact hact r v

/-- The original residual quotient has exactly the deleted five-point core action. -/
theorem point_quotient_deleted_block
    (L V : Subgroup G) (z : G)
    (hVX : V ≤ Centralizer.localTwoCore L z)
    (hsections : PointSectionActions V (Centralizer.commutatorSpace L V z)
      (zpowers z) (Centralizer.localResidual L z))
    (hprod : (centralizer ({z} : Set G)).pCoreIn 2 ⊔ V = Centralizer.localTwoCore L z)
    (hcap : V ⊓ (centralizer ({z} : Set G)).pCoreIn 2 =
      Centralizer.commutatorSpace L V z) :
    let C := centralizer ({z} : Set G)
    let R := Centralizer.localResidual L z
    ChapterC.IsAlternatingBlock ((R.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))) 5 := by
  let C := centralizer ({z} : Set G)
  let R := Centralizer.localResidual L z
  let X := Centralizer.localTwoCore L z
  let E := C.pCoreIn 2
  let W := Centralizer.commutatorSpace L V z
  let π := QuotientGroup.mk' (pCore 2 C)
  let H := (R.subgroupOf C).map π
  have hRC : R ≤ C := (Centralizer.localResidual_le L z).trans inf_le_right
  have hXR : X ≤ R := Centralizer.localTwoCore_le L z
  have hVR : V ≤ R := hVX.trans hXR
  have hER : E ≤ R := (le_sup_left.trans hprod.le).trans hXR
  let f : R →* H := (π.subgroupMap (R.subgroupOf C)).comp
    (subgroupOfEquivOfLe hRC).symm.toMonoidHom
  have hf : Function.Surjective f := (π.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hRC).symm.surjective
  have hfval (r : R) : (f r : C ⧸ pCore 2 C) = π (inclusion hRC r) := rfl
  have hfk : f.ker = E.subgroupOf R := by
    ext r
    change f r = 1 ↔ (r : G) ∈ E
    rw [Subtype.ext_iff,hfval]
    change π (inclusion hRC r)=1 ↔ (r : G) ∈ (pCore 2 C).map C.subtype
    change ((inclusion hRC r : C) : C ⧸ pCore 2 C)=1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hr
      exact mem_map_of_mem C.subtype hr
    · rintro ⟨c,hc,he⟩
      have hec : c = inclusion hRC r := Subtype.ext he
      rw [←hec]
      exact hc
  have hk : IsPGroup 2 f.ker := hfk.symm ▸ (isPGroup_pCoreIn 2 C).comap_subtype
  have hX : X.subgroupOf R = pCore 2 R := comap_map_eq_self_of_injective R.subtype_injective _
  have hmap : (V.subgroupOf R).map f = pCore 2 H := by
    have hh := congrArg (Subgroup.map f) (congrArg (fun A : Subgroup G => A.subgroupOf R) hprod)
    have hkmap : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff f.ker).mpr le_rfl
    rw [subgroupOf_sup hER hVR,Subgroup.map_sup,hX,←hfk,hkmap,bot_sup_eq] at hh
    have hm : (pCore 2 R).map f = pCore 2 H := by
      rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self_of_surjective hf]
    exact hh.trans hm
  let g : V →* pCore 2 H := {
    toFun := fun v => ⟨f (inclusion hVR v),hmap ▸ mem_map_of_mem f v.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul (f.comp (inclusion hVR)) a b) }
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨r,hr,he⟩ := hmap.ge x.property
    exact ⟨⟨r,hr⟩,Subtype.ext he⟩
  obtain ⟨hRV,_,eR,_,_,_,_,q,hq,hqker,hact⟩ := hsections
  have hgker : g.ker = q.ker := by
    rw [hqker]
    ext v
    change g v=1 ↔ (v : G) ∈ W
    rw [Subtype.ext_iff]
    change f (inclusion hVR v)=1 ↔ (v : G) ∈ W
    change inclusion hVR v ∈ f.ker ↔ _
    rw [hfk]
    exact ⟨fun hv => hcap.le ⟨v.property,hv⟩,fun hv => (hcap.ge hv).2⟩
  let : Group.IsPerfect R := Group.IsPerfect.map _
  exact block_of_full_core_image V R hVR hRV f hf hk eR g hg (fun _ => rfl) q hq hgker hact

open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The source SQTK condition excludes a normalized full-Sylow deleted-five local block. -/
theorem no_deleted_five_local_block
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) (B : Subgroup G) (hb : ChapterC.IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) : False := by
  obtain ⟨K,⟨hK,hBK⟩,_⟩ := Chapter1.Section02.containment_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) G hG hO S B hl
  let := alternatingFive_containing_component_quasisimple hG hO hK hBK hb
  obtain ⟨P,hP,hl'⟩ := exists_local_sylow_restriction S hl hBK hK.subnormal
  have hb' : ChapterC.IsAlternatingBlock (B.subgroupOf K) 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hBK).symm hb
  have hn' : (P : Subgroup K) ≤ normalizer (B.subgroupOf K : Set K) := by
    rw [hP,←subgroupOf_normalizer_eq hBK]
    exact comap_mono hn
  have hne : B.subgroupOf K ≠ ⊤ := by
    intro he
    have hBK' : B=K := le_antisymm hBK (subgroupOf_eq_top.mp he)
    have hcore : pCore 2 B = ⊥ := by
      apply (map_eq_bot_iff_of_injective (pCore 2 B) B.subtype_injective).mp
      exact bot_unique ((pCoreIn_le_of_subnormal 2 (hBK'.symm ▸ hK.subnormal)).trans hO.le)
    have hc := hb.blockU_card
    simp only [ChapterC.blockU,hcore,commutator_bot_left,Nat.card_eq_fintype_card] at hc
    norm_num at hc
  exact ChapterC.no_quasisimple_alternatingFive_full_sylow (hG.subgroup K) P _ hb' hl' hn' hne

/-- Apply the SQTK sieve to the original point centralizer quotient, retaining
its original Sylow and the actual local-component restriction. -/
theorem point_quotient_exclusion
    (L V : Subgroup G) (T : Sylow 2 G) (z : G)
    (hQ : IsSQTK KnownSimple.IsKnownSimple
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcomp : ((Centralizer.localResidual L z).subgroupOf
      (normalizer (L : Set G) ⊓ centralizer ({z} : Set G))).IsCComponent)
    (hVX : V ≤ Centralizer.localTwoCore L z)
    (hsections : PointSectionActions V (Centralizer.commutatorSpace L V z)
      (zpowers z) (Centralizer.localResidual L z))
    (hprod : (centralizer ({z} : Set G)).pCoreIn 2 ⊔ V = Centralizer.localTwoCore L z)
    (hcap : V ⊓ (centralizer ({z} : Set G)).pCoreIn 2 =
      Centralizer.commutatorSpace L V z) : False := by
  let C := centralizer ({z} : Set G)
  let R := Centralizer.localResidual L z
  let π := QuotientGroup.mk' (pCore 2 C)
  let S := T.subtype hTC
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  have hRC : R ≤ C := (Centralizer.localResidual_le L z).trans inf_le_right
  have hRM : R ≤ normalizer (L : Set G) ⊓ C :=
    (Centralizer.localResidual_le L z).trans (inf_le_inf_right _ L.le_normalizer)
  have hlocal : R ∈ localCComponents (T : Subgroup G) :=
    hcomp.subgroupOf_of_le le_sup_left (sup_le hRM (le_inf hTL hTC))
  have hlocalC : R.subgroupOf C ∈ localCComponents S := local_restrict hlocal hRC
  let : Group.IsSolvable π.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 C)).ker
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
    infer_instance
  have hlocalQ : (R.subgroupOf C).map π ∈ localCComponents P :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hlocalC π
  have hnormC : (S : Subgroup C) ≤ normalizer (R.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hRC]
    exact comap_mono (point_commutator_normalizes L V (T : Subgroup G) z hTL hTV hTC).1
  have hnormQ : (P : Subgroup (C ⧸ pCore 2 C)) ≤
      normalizer ((R.subgroupOf C).map π : Set _) :=
    (map_mono hnormC).trans (le_normalizer_map π)
  exact no_deleted_five_local_block hQ (pCore_quotient_pCore_eq_bot 2) P _
    (point_quotient_deleted_block L V z hVX hsections hprod hcap) hlocalQ hnormQ

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
