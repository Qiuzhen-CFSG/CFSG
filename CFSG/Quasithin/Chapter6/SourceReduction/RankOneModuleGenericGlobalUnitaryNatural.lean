module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNaturalModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction

/-!
# The original proper unitary image as a natural block

For K = O²(H), Q = O₂(K), R = O₂(J), the actual map K → J/R has
kernel K ∩ R. In the proper-intersection branch its Hermitian coordinates
construct a natural SL₂ block of field order 2^m, with its full two-core
as commutator module. The proved core order equals the natural module order,
so the center of this image is trivial.

Restriction of the original local family to J and passage through its
literal two-core quotient retain a full Sylow, exactly the image of T ∩ J.
This Sylow normalizes the same proper image. The containing quotient is
SQTK and is itself a C-component. These are the source inputs for the next
proper-embedding selection, including the degree-two unitary extension.

The Chapter12 companion applies these results to its remaining overcomponent.
The (S)L₃ embedding selection and second-parabolic contradiction are still
needed for unitary maximality. The other outstanding rows, exhaustive amalgam
comparison and ambient recognition remain separate obligations of the global
assembly. Source: Aschbacher–Smith 5.2.8, printed pp.652–653
(`refs/quasithin.pdf`), using the earlier local quotient and restriction results.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]

private theorem local_overcomponent_embedding_context
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKJ : K < J) (hRK : J.pCoreIn 2 ≤ normalizer (K : Set G))
    (hpK : Group.IsPerfect K) :
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ.le)
    IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) ∧
      (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent ∧ f.range ≠ ⊤ ∧
      ∃ S : Sylow 2 J, (S : Subgroup J) = (T : Subgroup G).subgroupOf J ∧
        (let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
         f.range ∈ ChapterA.Section03.localCComponents Sb ∧
           (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (f.range : Set _)) := by
  let X := J ⊔ (T : Subgroup G)
  let JX := J.subgroupOf X
  let eJ : JX ≃* J := subgroupOfEquivOfLe le_sup_left
  let TX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  obtain ⟨P,hP⟩ := TX.exists_subgroupOf_eq_of_subnormal JX hJ.1.subnormal
  let S := P.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hSJ : (S : Subgroup J) = (T : Subgroup G).subgroupOf J := by
    change (P : Subgroup JX).map eJ.toMonoidHom = _
    rw [hP]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hy
      exact ⟨eJ.symm y,hy,eJ.apply_symm_apply y⟩
  have hSK : (S : Subgroup J) ≤ normalizer (K.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hKJ.le]
    rw [hSJ]
    exact comap_mono hTK
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp (inclusion hKJ.le)
  let B := f.range
  have hBmap : B = (K.subgroupOf J).map q := by
    change (q.comp (inclusion hKJ.le)).range = _
    rw [MonoidHom.range_comp,inclusion_range]
  let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hnorm : (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (B : Set _) := by
    rw [hBmap]
    exact (map_mono hSK).trans (le_normalizer_map q)
  have hb : B ∈ ChapterA.Section03.localCComponents Sb := by
    have hl := ChapterA.Section03.SourceEmbeddings.local_restrict hK.1 hKJ.le
    rw [←hSJ] at hl
    let : Group.IsSolvable q.ker := by
      rw [QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
      infer_instance
    change B ∈ ChapterA.Section03.localCComponents ((S : Subgroup J).map q)
    simpa only [hBmap] using
      Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hne : B ≠ ⊤ := by
    intro ht
    let D := K.subgroupOf J
    have hgen : D ⊔ pCore 2 J = ⊤ := by
      have hh := congrArg (Subgroup.comap q) ht
      rw [hBmap,comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
      exact hh
    have hnD : D.Normal := (normalizer_eq_top_iff).mp (by
      have hh : D ⊔ pCore 2 J ≤ normalizer (D : Set J) := by
        refine sup_le D.le_normalizer ?_
        rw [←subgroupOf_normalizer_eq hKJ.le]
        intro x hx
        exact hRK (mem_map_of_mem J.subtype hx)
      rw [hgen] at hh
      exact top_unique hh)
    let := hnD
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hKJ.le).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKJ.le).symm.surjective
    let : Group.IsPerfect J := Chapter1.mem_L_isPerfect hJ
    have hDtop : D = ⊤ :=
      (residuals_of_perfect_normal_sup_twoGroup D (pCore 2 J) pCore_isPGroup hgen).2.symm.trans
        solvableResidual_eq_top
    exact hKJ.ne (le_antisymm hKJ.le (subgroupOf_eq_top.mp hDtop))
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hsq := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hJ.2.2
  let eqJ : JX.map qX ≃* (J ⧸ pCore 2 J) :=
    (cComponentTwoCoreQuotientEquiv hJ.1).symm.trans
      (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) :=
    (IsSQTK.equiv eqJ).mp (hsq.subgroup _)
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := X)
    have hh : (⊤ : Subgroup (JX.map qX)).IsCComponent := by
      simpa only [subgroupOf_self] using (hJ.1.map_quotient (pCore 2 X)).subgroupOf le_rfl
    simpa only [map_top_of_surjective eqJ.toMonoidHom eqJ.surjective] using hh.map_equiv eqJ
  exact ⟨hsqJ,htop,hne,S,hSJ,hb,hnorm⟩

section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- The literal proper image is a centerless natural SL₂ block, with its
entire two-core as its commutator module. The module isomorphism is obtained
from the actual Hermitian coordinates and original quotient map. -/
theorem Preparation.unitary_overcomponent_proper_image_block
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
    ChapterC.IsL2EvenBlock f.range m ∧
      pCore 2 f.range = ChapterC.blockU f.range ∧ center f.range = ⊥ := by
  let K := residual H
  let P := pCore 2 K
  let Q := K.pCoreIn 2
  let R := J.pCoreIn 2
  let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
  let r := f.rangeRestrict
  obtain ⟨_,hNQ,hnot,_,hZN,_⟩ :=
    d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ
  obtain ⟨_,_,_,_,_,_,_,_,_,hZK⟩ := d.unitary_core_structure h hH.1.1.2 hp m hm he
  obtain ⟨hker,_,hel,_,_⟩ := d.unitary_overcomponent_quotient_image h hH hp m hm he hJ hKJ
  have hrker : r.ker = R.subgroupOf K := f.ker_rangeRestrict.trans hker
  have hN : r.ker ≤ P := by
    rw [hrker]
    intro x hx
    exact (mem_map_iff_mem K.subtype_injective).mp (hNQ ⟨x.property,hx⟩)
  have hZ : ((center P).map P.subtype).map K.subtype = (center Q).map Q.subtype :=
    map_embeddedCenter P K.subtype K.subtype_injective
  have hz : (center P).map P.subtype ≤ r.ker := by
    rw [hrker]
    intro x hx
    exact (hZN (hZ ▸ mem_map_of_mem K.subtype hx)).2
  have hnz : ¬ r.ker ≤ (center P).map P.subtype := by
    rw [hrker]
    intro hh
    apply hnot
    intro x hx
    have hxc := hZK (hh (show (⟨x,hx.1⟩ : K) ∈ R.subgroupOf K from hx.2))
    exact mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hxc ⟨y,hy⟩))
  have hne : r.ker ≠ P := by
    rw [hrker]
    intro hh
    apply hQR
    rintro x ⟨u,hu,rfl⟩
    exact (show u ∈ R.subgroupOf K from hh.symm ▸ hu)
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  obtain ⟨e⟩ := hf.2.2.2.1
  obtain ⟨hb,hc⟩ := UnitaryNatural.point_image_block m hm hf.1 e r
    f.rangeRestrict_surjective hN hz hnz hne hel
  refine ⟨hb,hc,?_⟩
  have hzle : center f.range ≤ ChapterC.blockU f.range := by
    rw [←hc,←hb.2.1.centralizer_blockU]
    exact center_le_centralizer _
  have hcard := (d.unitary_overcomponent_proper_quotient_core h hH hp m hm he hJ hKJ hQR).1
  have hprod := card_eq_card_quotient_mul_card_subgroup (ChapterC.blockFixed f.range)
  change Nat.card (ChapterC.blockU f.range) =
    Nat.card (ChapterC.BlockModule f.range) * Nat.card (ChapterC.blockFixed f.range) at hprod
  have hcardU : Nat.card (ChapterC.blockU f.range) = (2^m)^2 := by
    rw [←hc]
    exact hcard
  rw [hcardU,hb.module_card,pow_mul] at hprod
  have hone : Nat.card (ChapterC.blockFixed f.range) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2^m)^2)
    simpa only [mul_one] using hprod.symm
  have hzcard : Nat.card (center f.range) = 1 := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hzle).toEquiv]
    exact hone
  exact (center f.range).eq_bot_of_card_eq hzcard

/-- The original full Sylow gives the literal proper quotient image its
local C-component membership and normalization. Its containing quotient is
an SQTK group and a C-component, as required by the source embedding theorem. -/
theorem Preparation.unitary_overcomponent_embedding_context
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J) :
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ.le)
    IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) ∧
      (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent ∧ f.range ≠ ⊤ ∧
      ∃ S : Sylow 2 J, (S : Subgroup J) = (T : Subgroup G).subgroupOf J ∧
        (let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
         f.range ∈ ChapterA.Section03.localCComponents Sb ∧
           (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (f.range : Set _)) := by
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  have hK := residual_binary_mem_local hH.1.1 hp hf.1 hf.2.2.2.2
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hRK := ((d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ.le).1.trans
    (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)).trans hTK
  exact local_overcomponent_embedding_context h.qtke hK hJ hTK hKJ hRK hp

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
