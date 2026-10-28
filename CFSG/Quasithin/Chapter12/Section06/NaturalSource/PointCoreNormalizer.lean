module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointResidual
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullAction
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ThompsonSource
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalThompson
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.FourBlock.SeedCore
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Thompson control of the original singular-point two-core

In the branch C_V(L)=1, extend the original six-space coordinates to LT.
The point centralizer in LT is exactly L1T. Its intrinsic two-core is the
original R1, contains Q=O2(LT), and lies in the unchanged Sylow T.
The B.3 nonoffender theorem for the six-dimensional permutation quotient
forces every maximum elementary subgroup of R1 into the action kernel Q.
Thompson heredity gives J(R1)=J(Q), so original uniqueness puts N_G(R1) in M.

The full original V, its fixed-space quotient projection, and the same
Sylow-fixed nonidentity point are retained. Vanishing of C_V(L) and the
stated invariance hypotheses remain explicit earlier-source inputs.
This supplies the normalizer premise in the cubic A7 branch of 12.6.26;
it does not assert that branch's model contradiction or the natural reduction.
Source: Aschbacher--Smith, 12.6.1(4), 12.6.26, printed pp.823,832.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06

private theorem maximum_image_isOffender_natural
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (q : X →* Equiv.Perm (Fin 8))
    (E : Additive U ≃ₗ[ZMod 2] natural (Fin 8))
    (he : ∀ x u, E (Additive.ofMul (MulAut.conjNormal x u)) =
      naturalRepresentation (Fin 8) (q x) (E (Additive.ofMul u)))
    (hk : q.ker = centralizer (U : Set X))
    (R A : Subgroup X) (hUR : U ≤ R)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hne : ¬ A ≤ q.ker) :
    IsOffender (naturalRepresentation (Fin 8)) (A.map q) := by
  let qr := q.rangeRestrict
  have hkr : qr.ker = centralizer (U : Set X) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hk
  let rho := Representation.NormalElementaryQuotient.representation U qr
    q.rangeRestrict_surjective hkr
  have ho := Representation.NormalElementaryQuotient.maxElementary_isOffender
    U qr q.rangeRestrict_surjective hkr R A hUR hA (by
      simpa only [qr,MonoidHom.ker_rangeRestrict] using hne)
  have hE (x : q.range) (u : Additive U) :
      E (rho x u) = naturalRepresentation (Fin 8) x.val (E u) := by
    obtain ⟨x,rfl⟩ := q.rangeRestrict_surjective x
    have hh := Representation.NormalElementaryQuotient.representation_apply
      U qr q.rangeRestrict_surjective hkr x u
    have hu : (rho (qr x) u).toMul = MulAut.conjNormal x u.toMul := Subtype.ext hh
    rw [show rho (qr x) u = Additive.ofMul (MulAut.conjNormal x u.toMul) from hu]
    exact he x u.toMul
  have hh := ho.map_equivariant rho (naturalRepresentation (Fin 8)) q.range.subtype
    q.range.subtype_injective E hE
  rw [map_map] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual local point group is the centralizer in LT; no quotient
identification is substituted for equality in the original ambient group. -/
theorem SourceHypothesis.original_point_join_eq
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) =
      LT T L ⊓ (D.fullSetup hZ T z).Gz := by
  let F := D.fullSetup hZ T z
  have hG : F.Gz = Gv (z : G) := F.Gz_eq
  have hL : F.L₁ = Lv L (z : G) := by
    change (pResidual 2 (L ⊓ F.Gz : Subgroup G)).map (L ⊓ F.Gz).subtype = _
    change (pResidual 2 (L ⊓ F.Gz : Subgroup G)).map (L ⊓ F.Gz).subtype =
      (pResidual 2 (L ⊓ Gv (z : G) : Subgroup G)).map (L ⊓ Gv (z : G)).subtype
    rw [hG]
  have hTG : (T : Subgroup G) ≤ F.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two F.V₁ (F.point_card hz))
  have hTv : Tv T (z : G) = (T : Subgroup G) := by
    change (T : Subgroup G) ⊓ Gv (z : G) = _
    rw [←hG]
    exact inf_eq_left.mpr hTG
  have hTJ : (T : Subgroup G) ≤ LT T L ⊓ Gv (z : G) :=
    le_inf le_sup_right (hG ▸ hTG)
  have hs : Chapter1.IsSylowIn 2 (Tv T (z : G)) (LT T L ⊓ Gv (z : G)) := by
    rw [hTv]
    exact ⟨T.subtype hTJ,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ]⟩
  have hh := localCentralizer_eq_Lv_sup_Tv S.chosen.sylow_normalizes_component (z : G) hs
  rw [hTv,←hG,←hL] at hh
  exact hh.symm


/-- The literal R₁ agrees with the intrinsic two-core of the point
centralizer in LT, and contains Q. -/
theorem SourceHypothesis.original_point_core_eq
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    (D.fullSetup hZ T z).R₁ = Rv T L (z : G) ∧
      Q T L ≤ (D.fullSetup hZ T z).R₁ ∧
      (D.fullSetup hZ T z).R₁ ≤ (T : Subgroup G) := by
  let F := D.fullSetup hZ T z
  have he : F.R₁ = Rv T L (z : G) := by
    change (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [S.original_point_join_eq D hZ z hz hTz]
    have hG : F.Gz = Gv (z : G) := F.Gz_eq
    rw [hG]
    rfl
  refine ⟨he,he.symm ▸ Q_le_Rv S.chosen z,?_⟩
  let B := F.L₁ ⊔ (T : Subgroup G)
  have ht : (T : Subgroup G) ≤ B := le_sup_right
  exact (pCoreIn_le_sylow B (T.subtype ht)).trans_eq
    (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le ht])

/-- Source 12.6.1(4) on the actual six-space branch. The B.3 nonoffender
calculation is applied to the literal original point core. -/
theorem SourceHypothesis.original_point_core_thompson
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    elementaryAbelianMaxJ (D.fullSetup hZ T z).R₁ = elementaryAbelianMaxJ (Q T L) ∧
      normalizer ((D.fullSetup hZ T z).R₁ : Set G) ≤ M L := by
  let F := D.fullSetup hZ T z
  let J := LT T L
  let C := J ⊓ F.Gz
  let U := V.subgroupOf J
  have hVJ : V ≤ J := S.chosen.le_component.trans le_sup_left
  have hJV : J ≤ normalizer (V : Set G) := sup_le S.chosen.normalizes hTV
  let : U.Normal := normal_subgroupOf_of_le_normalizer hJV
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVJ
  let eU : Additive U ≃ₗ[ZMod 2] Additive V :=
    { (subgroupOfEquivOfLe hVJ).toAdditive with
      map_smul' := ZMod.map_smul (subgroupOfEquivOfLe hVJ).toAdditive }
  let E := eU.trans (D.fullLinearCoordinates hZ)
  obtain ⟨f,hf,ha,hk⟩ := D.exists_full_permutation_action S.chosen hZ hTV
  have hke : f.ker = pCore 2 J := by
    apply map_injective J.subtype_injective
    rw [hk]
    change ((centralizer (V : Set G)).subgroupOf J).map J.subtype = _
    rw [subgroupOf_map_subtype,inf_comm]
    exact S.join_centralizer_eq_core hTV
  have hkc : f.ker = centralizer (U : Set J) := by
    rw [hk]
    ext x
    constructor
    · intro hx u hu
      exact Subtype.ext (hx u hu)
    · intro hx u hu
      exact congrArg J.subtype (hx ⟨u,hVJ hu⟩ hu)
  have hE (x : J) (u : U) : E (Additive.ofMul (MulAut.conjNormal x u)) =
      naturalRepresentation (Fin 8) (f x) (E (Additive.ofMul u)) := ha x ⟨u.val, u.property⟩
  let w := (D.fullCoordinates hZ z).toAdd
  have hw : w ≠ 0 := by
    intro hw
    exact hz ((D.fullCoordinates hZ).injective (hw.trans (D.fullCoordinates hZ).map_one.symm))
  have hfix (x : J) : naturalRepresentation (Fin 8) (f x) w = w ↔ x.val ∈ F.Gz := by
    rw [←ha x z]
    change D.fullCoordinates hZ (V.normalizerMonoidHom ⟨x.val,hJV x.property⟩ z) =
      D.fullCoordinates hZ z ↔ _
    rw [(D.fullCoordinates hZ).injective.eq_iff,F.Gz_eq,mem_centralizer_singleton_iff]
    constructor
    · intro hh
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
    · intro hh
      apply Subtype.ext
      change x.val*z.val*x.val⁻¹ = z.val
      change x.val*z.val = z.val*x.val at hh
      rw [hh,mul_inv_cancel_right]
  have hH : alternatingGroup (Fin 8) ≤ f.range := by
    intro k hkalt
    obtain ⟨l,hl⟩ := D.groupEquiv.surjective ⟨k,hkalt⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (conjugation L V S.chosen.normalizes).ker l
    exact ⟨⟨l.val,mem_sup_left l.property⟩,(hf l).trans (congrArg Subtype.val hl)⟩
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let q : L →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker)
  have hq : Function.Surjective q := D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pbar := P.mapSurjective (f := q.comp e.toMonoidHom) (hq.comp e.surjective)
  have hTG : (T : Subgroup G) ≤ F.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two F.V₁ (F.point_card hz))
  have hfw : w ∈ fixedSpace (alternatingNaturalRepresentation (Fin 8)) Pbar := by
    rintro ⟨k,hkQ⟩
    obtain ⟨a,haP,rfl⟩ := hkQ
    change naturalRepresentation (Fin 8) (q (e a)).val w = w
    change naturalRepresentation (Fin 8)
      (D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker (e a))).val w = w
    rw [←hf (e a)]
    apply (hfix _).mpr
    apply hTG
    rw [hP] at haP
    exact haP
  let Z := Submodule.span (ZMod 2) ({w} : Set (natural (Fin 8)))
  have hZne : Z ≠ ⊥ := by
    intro he
    apply hw
    have h : w ∈ Z := Submodule.subset_span (Set.mem_singleton w)
    rwa [he,Submodule.mem_bot] at h
  have hZfix : Z ≤ fixedSpace (alternatingNaturalRepresentation (Fin 8)) Pbar :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hfw)
  have hC : (C.subgroupOf J).map f = subspaceKernel (naturalRepresentation (Fin 8)) Z f.range := by
    ext k
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨⟨x,rfl⟩,?_⟩
      intro v hv
      obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,(hfix x).mpr hx.2]
    · rintro ⟨⟨x,rfl⟩,hx⟩
      exact ⟨x,⟨x.property,(hfix x).mp (hx w (Submodule.subset_span (Set.mem_singleton w)))⟩,rfl⟩
  have hR : (F.R₁.subgroupOf J).map f =
      (subspaceKernel (naturalRepresentation (Fin 8)) Z f.range).pCoreIn 2 := by
    rw [←hC,←map_pCoreIn_of_ker_isPGroup f (hke.symm ▸ pCore_isPGroup)]
    rw [pCoreIn_subgroupOf 2 C J inf_le_left]
    congr 2
    exact congrArg (fun B : Subgroup G => B.pCoreIn 2) (S.original_point_join_eq D hZ z hz hTz)
  obtain ⟨_,hQR,hRT⟩ := S.original_point_core_eq D hZ z hz hTz
  have hUR : U ≤ F.R₁.subgroupOf J := comap_mono (S.chosen.le_core.trans hQR)
  have hJR : elementaryAbelianMaxJ (F.R₁.subgroupOf J) ≤ f.ker := by
    apply sSup_le
    intro B hB
    by_contra hn
    have ho := maximum_image_isOffender_natural U f E hE hkc
      (F.R₁.subgroupOf J) B hUR hB hn
    exact ChapterB.Offenders.Eight.FourBlock.no_seed_core_offender
      f.range hH Pbar Z hZne hZfix ho ((map_mono hB.1).trans_eq hR)
  have hRJ : F.R₁ ≤ J := hRT.trans le_sup_right
  have hJG : elementaryAbelianMaxJ F.R₁ ≤ Q T L := by
    rw [←map_subgroupOf_eq_of_le hRJ,
      elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective]
    exact (map_mono hJR).trans_eq (congrArg (map J.subtype) hke)
  have hj : elementaryAbelianMaxJ F.R₁ = elementaryAbelianMaxJ (Q T L) :=
    (elementaryAbelianMaxJ_eq_of_intermediate F.R₁ (Q T L) hJG hQR).symm
  exact ⟨hj,(normalizer_le_normalizer_elementaryAbelianMaxJ F.R₁).trans
    (hj ▸ S.core_thompson_normalizer)⟩

end CFSG.Quasithin.Chapter12.Section06
