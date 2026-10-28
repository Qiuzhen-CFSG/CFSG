module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.HermitianAction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.CenterKernel
public import Theory.GroupTheory.ElementaryThompsonFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.CoreCenters
public import CFSG.Quasithin.ChapterD.Section03.HermitianMultiplicity
public import CFSG.Quasithin.Chapter7.NormalizedSource.Automizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel

/-!
# The full Sylow Thompson subgroup in the prepared U₅(4) row

The geometric plane residual identifies its core center with the actual
Hermitian SL₂(16) module. Proper-K supplies SQTK for this quotient; the full
binary normalizer has no FF offenders, so J(T) centralizes the center.
The native square-map calculation and the faithful Frattini action in the
characteristic-two full normalizer put every elementary generator of J(T)
in the plane core. Its involutions all lie in its center. Maximal elementary
order gives J(T)=Z(O₂(L)), including possible outer actors.

The same argument proves the inner identity, weak closure and Burnside
fusion control by N_G(L). Both source comparison orientations and the whole
right residual are retained. The nonfusion and Chapter12 companions use
these actual ambient conclusions.
Source: Aschbacher–Smith F.4.29(6), F.4.35, printed pp.289,292,
using B.2.7 and K.3.1.2 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
local instance : Algebra (ZMod 2) (fixedField 2) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space 2) :=
  Module.compHom (Space 2) (algebraMap (ZMod 2) (fixedField 2))

omit [Finite G] in
private theorem center_model_of_equiv (L : Subgroup G) (U : Model 4)
    (e : L ≃* PlaneCore.PlaneSemidirect U.form) :
    IsConjugationModel L ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
      (SL2.BinarySmall.hermitian 2) := by
  obtain ⟨b⟩ := SL2.BinarySmall.nonempty_hermitianFieldEquiv (K := U.F) 2
    (by simpa using U.local_field_card)
  let q := PlaneCore.hermitianProjection U.form e b
  have hq := PlaneCore.hermitianProjection_surjective U.form e b
  have hk := PlaneCore.hermitianProjection_ker U.form e b
  let eq : (L ⧸ pCore 2 L) ≃* SL(2,Field 2) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let f := PlaneCore.coreCenterHermitianEquiv U.form e U.rightLeviTrace
    U.rightLeviTrace_spec U.conjugation b
  let ec : pCore 2 L ≃* L.pCoreIn 2 :=
    (pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective
  let ez : center (pCore 2 L) ≃*
      (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype :=
    (centerCongr ec).trans ((center (L.pCoreIn 2)).equivMapOfInjective
      (L.pCoreIn 2).subtype (L.pCoreIn 2).subtype_injective)
  have hez (u : center (pCore 2 L)) : (ez u : G) = (u.val.val : G) := rfl
  refine ⟨eq,ez.symm.trans f,?_⟩
  intro l v
  have hh := PlaneCore.coreCenterHermitianEquiv_conjugation U.form e U.rightLeviTrace
    U.rightLeviTrace_spec U.conjugation b l (ez.symm v)
  change f ((centerCongr (MulAut.conjNormal l)) (ez.symm v)) =
    Multiplicative.ofAdd (SL2.BinarySmall.hermitian 2 (q l) (f (ez.symm v)).toAdd) at hh
  change (ez (f.symm (Multiplicative.ofAdd
    (SL2.BinarySmall.hermitian 2 (q l) (f (ez.symm v)).toAdd))) : G) = _
  rw [←hh,f.symm_apply_apply,hez]
  have hv : ((ez.symm v).val.val : G) = v.val :=
    (hez (ez.symm v)).symm.trans (congrArg Subtype.val (ez.apply_symm_apply v))
  change (l : G) * ((ez.symm v).val.val : G) * (l : G)⁻¹ = _
  rw [hv]

private theorem thompson_centralizes_of_nonFF (V S : Subgroup G)
    [IsElementaryAbelian 2 V] (hVS : V ≤ S)
    (hSN : S ≤ normalizer (V : Set G))
    (hn : ¬ IsFFModule (ChapterE.automizerRepresentation V)) :
    elementaryAbelianMaxJ S ≤ centralizer (V : Set G) := by
  let N := normalizer (V : Set G)
  let VN := V.subgroupOf N
  let SN := S.subgroupOf N
  let : VN.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsElementaryAbelian 2 VN := IsElementaryAbelian.subgroupOf V.le_normalizer
  let q := V.normalizerMonoidHom.rangeRestrict
  have hq := V.normalizerMonoidHom.rangeRestrict_surjective
  have hk : q.ker = centralizer (VN : Set N) := by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.normalizerMonoidHom_ker]
    ext g
    constructor
    · intro hg v hv
      exact Subtype.ext (hg v hv)
    · intro hg v hv
      exact congrArg N.subtype (hg ⟨v,V.le_normalizer hv⟩ hv)
  by_contra hJ
  have hJN : ¬ elementaryAbelianMaxJ SN ≤ q.ker := by
    intro hh
    apply hJ
    have hm := map_mono hh (f := N.subtype)
    rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,
      show SN.map N.subtype = S from map_subgroupOf_eq_of_le hSN] at hm
    intro x hx
    obtain ⟨g,hg,rfl⟩ := hm hx
    change g ∈ V.normalizerMonoidHom.rangeRestrict.ker at hg
    rw [MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker] at hg
    exact hg
  let ρ := Representation.NormalElementaryQuotient.representation VN q hq hk
  have hff := Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    VN q hq hk SN (fun v hv => hVS hv) hJN
  let e := subgroupOfEquivOfLe V.le_normalizer
  let E : Additive VN ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  apply hn
  apply hff.map_equivariant ρ (ChapterE.automizerRepresentation V)
    (MonoidHom.id _) Function.injective_id E
  intro a v
  obtain ⟨g,rfl⟩ := hq a
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg N.subtype
    (Representation.NormalElementaryQuotient.representation_apply VN q hq hk g v)


variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original plane-core center is the Hermitian module for the literal
quotient of L by its two-core, over the field of sixteen elements. -/
theorem Preparation.unitaryFive_plane_center_hermitian_model
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    IsConjugationModel L ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
      (SL2.BinarySmall.hermitian 2) := by
  rcases hc with ho | hr
  · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
  obtain ⟨hr⟩ := hr
  obtain ⟨_,⟨e⟩,_⟩ := d.unitaryFive_local_structure h hH.1.1.2 hp U hr
  exact center_model_of_equiv L U
    (e.trans (U.rightLocalImageEquiv.symm.trans U.rightLocalEquiv.symm))

/-- The full ambient automizer of the plane-core center has no FF offenders. -/
theorem Preparation.unitaryFive_plane_center_nonFF
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    letI : IsElementaryAbelian 2 ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) :=
      ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map (L.pCoreIn 2).subtype
    ¬ IsFFModule (ChapterE.automizerRepresentation
      ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)) := by
  let Q := L.pCoreIn 2
  let Z := (center Q).map Q.subtype
  let : IsElementaryAbelian 2 (center Q) :=
    (d.unitaryFive_plane_core_structure h hH hp U hc).2.1
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map Q.subtype
  have hnorm : normalizer (Z : Set G) = normalizer (L : Set G) :=
    d.unitaryFive_core_center_normalizers h hH hp U hc 0
  have hLN : L ≤ normalizer (Z : Set G) := hnorm.symm ▸ L.le_normalizer
  obtain ⟨e,f,hf⟩ := d.unitaryFive_plane_center_hermitian_model h hH hp U hc
  let : IsQuasisimple SL(2,Field 2) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by rw [GaloisField.card 2 4 (by decide)]; decide) (MulEquiv.refl _)
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup
      (L.subgroupOf (normalizer (L : Set G)))).knownSimple_of_equiv
      (subgroupOfEquivOfLe L.le_normalizer)
  have hmodel : IsSQTK KnownSimple.IsKnownSimple SL(2,Field 2) :=
    (ChapterE.Structure.sqtk_two_quotient hL (pCore 2 L) pCore_isPGroup).knownSimple_of_equiv e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let b : Additive Z ≃ₗ[ZMod 2] Space 2 :=
    { __ := f.toAdditiveLeft
      map_smul' := ZMod.map_smul f.toAdditiveLeft }
  have hn : ¬ IsFFModule (ChapterE.automizerRepresentation Z) := by
    apply Chapter7.NormalizedSource.automizer_nonFF Z L hLN hnorm.le
      (SL2.BinarySmall.hermitian 2) q (e.surjective.comp (QuotientGroup.mk'_surjective _)) b.symm
    · intro l v
      apply Additive.toMul.injective
      apply Subtype.ext
      change (f.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian 2 (q l) v)) : G) =
          (l : G) * (f.symm (Multiplicative.ofAdd v) : G) * (l : G)⁻¹
      have he := hf l (b.symm v).toMul
      change (f.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian 2 (q l) (f (f.symm (Multiplicative.ofAdd v))).toAdd)) : G) = _ at he
      simp only [f.apply_symm_apply] at he
      exact he
    · exact ChapterD.hermitian_normalizer_not_ff 2 hmodel (by decide)
  exact hn



/-- The center action detects exactly the original plane two-core inside L. -/
theorem Preparation.unitaryFive_plane_center_centralizer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    L ⊓ centralizer ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype : Set G) =
      L.pCoreIn 2 :=
  (d.unitaryFive_plane_center_hermitian_model h hH hp U hc).centralizer_eq_core
    (Representation.OrthogonalFourMinus.RankOne.hermitian_injective 2)

private theorem Preparation.unitaryFive_core_le_sylow
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) : L.pCoreIn 2 ≤ (T : Subgroup G) := by
  have hloc := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  have he : (normalizer (L : Set G)).pCoreIn 2 = L.pCoreIn 2 := hloc.twoCore_left
  have hh := pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype h.sylow_normalizes)
  rwa [he,Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes] at hh

/-- The full ambient Thompson subgroup centralizes the original plane-core center. -/
theorem Preparation.unitaryFive_thompson_centralizes_plane_center
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype : Set G) := by
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  let : IsElementaryAbelian 2 Z :=
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map (L.pCoreIn 2).subtype
  have hnorm : normalizer (Z : Set G) = normalizer (L : Set G) :=
    d.unitaryFive_core_center_normalizers h hH hp U hc 0
  exact thompson_centralizes_of_nonFF Z T
    ((map_subtype_le _).trans (d.unitaryFive_core_le_sylow h hH hp U hc))
    (hnorm.symm ▸ h.sylow_normalizes) (d.unitaryFive_plane_center_nonFF h hH hp U hc)

/-- The entire inner Sylow, rather than merely its plane core, has Thompson
subgroup equal to the original plane-core center. -/
theorem Preparation.unitaryFive_inner_thompson
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) =
      (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  let : IsElementaryAbelian 2 Z :=
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map (L.pCoreIn 2).subtype
  have hnorm : normalizer (Z : Set G) = normalizer (L : Set G) :=
    d.unitaryFive_core_center_normalizers h hH hp U hc 0
  have hZS : Z ≤ (T : Subgroup G) ⊓ L := le_inf
    ((map_subtype_le _).trans (d.unitaryFive_core_le_sylow h hH hp U hc))
    ((map_subtype_le _).trans (pCoreIn_le 2 L))
  have hjc := thompson_centralizes_of_nonFF Z ((T : Subgroup G) ⊓ L) hZS
    (inf_le_left.trans (hnorm.symm ▸ h.sylow_normalizes))
    (d.unitaryFive_plane_center_nonFF h hH hp U hc)
  have hjl : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) ≤ L :=
    sSup_le fun E hE => hE.1.trans inf_le_right
  have hjq := (le_inf hjl hjc).trans_eq (d.unitaryFive_plane_center_centralizer h hH hp U hc)
  have hjz : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) ≤ Z := by
    apply sSup_le
    intro E hE
    exact d.unitaryFive_plane_core_elementary_le_center h hH hp U hc E
      ((le_sSup hE).trans hjq) hE.2.1
  exact elementaryAbelianMaxJ_eq_of_elementary_overgroup _ _ hjz hZS inferInstance



/-- The original full Sylow has the same elementary Thompson subgroup as
its inner intersection, including all possible outer actors. -/
theorem Preparation.unitaryFive_thompson
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    elementaryAbelianMaxJ (T : Subgroup G) =
      (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
  let Q := L.pCoreIn 2
  let Z := (center Q).map Q.subtype
  let M := normalizer (L : Set G)
  let : IsElementaryAbelian 2 Z :=
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map Q.subtype
  have hloc := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  have hcore : M.pCoreIn 2 = Q := hloc.twoCore_left
  let ec : pCore 2 M ≃* Q :=
    ((pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hcore)
  have eparams : Nonempty (Q ≃* PlaneCore.Parameters U.form) := by
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    obtain ⟨hr⟩ := hr
    obtain ⟨_,⟨e⟩,_⟩ := d.unitaryFive_local_structure h hH.1.1.2 hp U hr
    exact ⟨((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
      ((LocalCoreTransport.coreEquiv 2 e).trans U.rightLocalImageCoreParameters)⟩
  obtain ⟨ep⟩ := eparams
  have hcentral := d.unitaryFive_thompson_centralizes_plane_center h hH hp U hc
  have hjz : elementaryAbelianMaxJ (T : Subgroup G) ≤ Z := by
    apply sSup_le
    intro E hE
    apply d.unitaryFive_plane_core_elementary_le_center h hH hp U hc E _ hE.2.1
    intro x hx
    let r : M := ⟨x,h.sylow_normalizes (hE.1 hx)⟩
    let : IsElementaryAbelian 2 E := hE.2.1
    have hr : r ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
    have hz : r ∈ centralizer ((center (pCore 2 M)).map (pCore 2 M).subtype : Set M) := by
      intro z hz
      obtain ⟨z,hz,rfl⟩ := hz
      apply Subtype.ext
      exact hcentral ((le_sSup hE) hx) z.val.val
        ⟨ec z,(centerCongr ec ⟨z,hz⟩).property,rfl⟩
    have hm := PlaneCore.involution_mem_core_of_center_centralizing U.form (ec.trans ep)
      U.rightLeviTrace U.rightLeviTrace_spec
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hloc.fitting_left) r hr hz
    have hxQ : x ∈ M.pCoreIn 2 := ⟨r,hm,rfl⟩
    change x ∈ Q
    rwa [hcore] at hxQ
  exact elementaryAbelianMaxJ_eq_of_elementary_overgroup _ _ hjz
    ((map_subtype_le _).trans (d.unitaryFive_core_le_sylow h hH hp U hc)) inferInstance

/-- The full Thompson normalizer is the original plane-residual normalizer. -/
theorem Preparation.unitaryFive_thompson_normalizer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) = normalizer (L : Set G) := by
  rw [d.unitaryFive_thompson h hH hp U hc]
  exact d.unitaryFive_core_center_normalizers h hH hp U hc 0

/-- Burnside fusion on the full plane-core center is controlled by N_G(L). -/
theorem Preparation.unitaryFive_plane_center_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    {x y : G} (hx : x ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hy : y ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) (hxy : IsConj x y) :
    ∃ g ∈ normalizer (L : Set G), g*x*g⁻¹ = y := by
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  let : IsElementaryAbelian 2 Z :=
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map (L.pCoreIn 2).subtype
  have hzc : Z ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [d.unitaryFive_thompson h hH hp U hc]
    exact Z.le_centralizer
  have hh := maxJ_controls_centralizer_fusion T (hzc hx) (hzc hy) hxy
  rwa [d.unitaryFive_thompson_normalizer h hH hp U hc] at hh

/-- The plane-core center is weakly closed in the full ambient Sylow. -/
theorem Preparation.unitaryFive_plane_center_weakly_closed
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (g : G) (hg : ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype).conjBy g ≤
      (T : Subgroup G)) :
    ((center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype).conjBy g =
      (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
  have hJ := d.unitaryFive_thompson h hH hp U hc
  have hh := elementaryAbelianMaxJ_map_eq_of_le (T : Subgroup G)
    (MulAut.conj g) (by rwa [hJ])
  simpa only [hJ,Subgroup.conjBy] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
