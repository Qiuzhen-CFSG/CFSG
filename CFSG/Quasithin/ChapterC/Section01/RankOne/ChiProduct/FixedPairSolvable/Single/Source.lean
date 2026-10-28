module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.LocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.Movement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.Restriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Ambient.Local
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable

/-!
# The original fixed-pair source in the solvable single-factor branch

Apply the fixed universal pair to the normal residual--Baumann join.
If its centralizer/normalizer control is proper, the same pair produces an
A₃ block. Its embedded residual is exactly the original O²(H), hence is
normal in H. The original Thompson movement and the support in the original
omega-center module are proved internally. This is precisely the full-Sylow
local block required by the subsequent C.1.27 ambient lift.

Source: Aschbacher--Smith C.1.26--28 and 14.1.11, printed pp.132--134,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original residual itself is the moving A₃ block. No subnormality,
block, natural-module or kernel-two-group premise is required. -/
theorem residual_alternatingThree_of_fixed_pair_escape
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hfit : generalizedFitting G = pCore 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hproper : control T D ≠ ⊤) (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))
    (habel : IsMulCommutative ((T : Subgroup G).map (QuotientGroup.mk' (centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))))) :
    let U := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
    IsBlock (pResidual 2 G) ∧ IsAlternatingBlock (pResidual 2 G) 3 ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ ∧
      ⁅U,pResidual 2 G⁆ ≠ ⊥ := by
  let U := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  have hU : IsPReduced 2 U := omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  let : IsElementaryAbelian 2 U := hU.elementary
  have hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
    apply thompson_moves_of_escape T D ⊤ U le_top le_top
      (inf_le_left.trans le_normalClosure)
    intro hh
    exact hproper (top_unique hh)
  have hlocal := selected_inLocalClass_of_abelian_action T hP hfit hJ hrank hsolv habel
  let N := pResidual 2 G ⊔ baumann (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ control T D :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_control T D)
  have hout : ¬ N ≤ control T D := by
    intro hh
    apply hproper
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top T]
    exact sup_le (le_sup_left.trans hh) hTN
  have hblock : BlockAlternative N := by
    apply FixedPair.fixed_pair_block_of_escape T D hD ⊤ N le_top le_sup_right hlocal
    simpa only [control,top_inf_eq] using hout
  have hsG := solvable_of_reduced_minimalParabolic_action T hP U hU hJ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hsolv
  let : Group.IsSolvable G := hsG
  have hmap : (pResidual 2 N).map N.subtype = pResidual 2 G :=
    embedded_pResidual_join_pGroup (pResidual 2 G) (baumann (T : Subgroup G))
      (isPPerfect_pResidual 2) (T.isPGroup'.to_le inf_le_left) le_normalizer_of_normal
  let e : pResidual 2 N ≃* pResidual 2 G :=
    ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have ha : IsAlternatingBlock (pResidual 2 G) 3 := by
    rcases hblock.2 with ⟨n,hn⟩ | ha
    · exact hn.not_solvable.elim
    · exact Solvable.isAlternatingBlock_of_equiv e ha
  have hb : IsBlock (pResidual 2 G) :=
    ⟨inferInstance,ha.2.1,(inferInstance : (pResidual 2 G).Normal).isSubnormal⟩
  obtain ⟨_,_,h3,_⟩ := CubicLocal.reduced_abelian_sylow_action T hP U hU hJ hsolv habel
  have hm := residual_moved_of_cubic_image T hP U hU hJ q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot h3
  have hne : ⁅U,pResidual 2 G⁆ ≠ ⊥ := by
    intro he
    have hRC : pResidual 2 G ≤ centralizer (U : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hz : (pResidual 2 G).map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr
      (by simpa only [q,QuotientGroup.ker_mk'] using hRC)
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)] at hz
    rw [hz,card_bot] at h3
    omega
  exact ⟨hb,ha,hm,SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator _ U hb hne,hne⟩

/-- The literal C.1.27 consumer: the selected minimal parabolic contains the
full original Sylow, and its same residual maps to a moving ambient A₃ block. -/
theorem ambient_alternatingThree_of_single_minimal_escape
    (T : Sylow 2 G) (hfit : generalizedFitting G = pCore 2 G)
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))
    (habel : IsMulCommutative ((T : Subgroup G).map (QuotientGroup.mk' (centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤)
    (D : CharacteristicPair (baumann (T.subtype hTH : Subgroup H)))
    (hD : D.Universal.{u,u}) (hproper : control (T.subtype hTH) D ≠ ⊤) :
    let A := (pResidual 2 H).map H.subtype
    let V := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
    IsBlock A ∧ IsAlternatingBlock A 3 ∧
      A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU A).map A.subtype = ⁅V,A⁆ ∧ ⁅V,A⁆ ≠ ⊥ := by
  have hc := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit
  have hcH := centralizer_pCore_le_of_pCore_le H hc
    ((pCore_isPGroup.le_sylow_of_normal T).trans hTH)
  let U := normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)
  have hmap := omegaClosure_map_le T H hTH
  have hsH := solvable_local_action _ H U hmap hsolv
  have haH := abelian_sylow_local_action T _ H hTH U hmap habel
  obtain ⟨hb,ha,hm,hu,_⟩ := residual_alternatingThree_of_fixed_pair_escape (T.subtype hTH) hP
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mpr hcH) D hD hproper
    ((Theory.GroupTheory.primeRank_le_of_injective 3 H.subtype H.subtype_injective).trans hrank) hsH haH
  apply Ambient.local_alternatingThree_maps_to_ambient T hc H hTH (pResidual 2 H) hb ha hm
  · exact (map_mono (f := H.subtype) (hu.le.trans (commutator_le_left U _))).trans hmap
  · exact hsolv
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
