module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt.Reduction

/-!
# Triple-Mathieu action at the original G,T

This replays the source 14.7.36 argument using only same-G,T earlier
structural and alternative results. The original groups, quotients and
actions are retained; no later 14.7.47 input is assumed.
Source: Aschbacher–Smith, printed p.1059, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section06.OddCriticalPair.Selection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem reduced_triple_mathieu_star_structure_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let B := C.map q
    B.Normal ∧ Nonempty (B ≃* Sporadic.Mathieu.M22TripleCover) ∧
      generalizedFitting (HStar I) = B ∧
      B ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map q = ⊤ ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ((F.Li L 1).subgroupOf I).map q = (center B).map B.subtype := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  obtain ⟨hn,_,hz,hpn,_,_,_⟩ := local_triple_mathieu_central_point_at
    d h hab structural previous faithful earlier I hI C hC e
  let := hn
  let hnB : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple B :=
    (WholeResidualAssembly.GuardedSource.local_component_star_isComponent h hab structural previous faithful I hI C hC).2
  let eB : B ≃* Sporadic.Mathieu.M22TripleCover :=
    (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  have hg : B ⊔ ((T : Subgroup G).subgroupOf I).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 (HStar I ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B _ (T.isPGroup'.comap_subtype.map q) hg
  refine ⟨hnB,⟨eB⟩,generalizedFitting_eq_of_quasisimple_two_quotient B hquot
    (pCore_quotient_pCore_eq_bot 2),?_,hpn,hz⟩
  apply top_unique
  rw [←hg]
  exact sup_le_sup_left (map_mono (subgroupOf_mono I le_sup_right)) _

theorem reduced_triple_mathieu_point_centralizer_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    centralizer ((((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) :
      Set (HStar I)) = C.map (QuotientGroup.mk' (pCore 2 I)) := by
  let B := C.map (QuotientGroup.mk' (pCore 2 I))
  obtain ⟨hn,⟨eB⟩,hfit,_,_,hz⟩ := reduced_triple_mathieu_star_structure_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hn
  rw [hz]
  apply le_antisymm
  · intro t ht
    let a : MulAut B := MulAut.conjNormal t
    let b := MulAut.congr eB a
    have hfix : a (eB.symm Sporadic.Mathieu.M22TripleCover.scalar) =
        eB.symm Sporadic.Mathieu.M22TripleCover.scalar := by
      apply Subtype.ext
      have hs := mem_centralizer_iff.mp ht _ (mem_map_of_mem B.subtype
        (Sporadic.Mathieu.M22TripleCover.scalar_mem_center_of_equiv eB))
      change (eB.symm Sporadic.Mathieu.M22TripleCover.scalar : HStar I) * t =
        t * (eB.symm Sporadic.Mathieu.M22TripleCover.scalar : HStar I) at hs
      change t * _ * t⁻¹ = _
      rw [←hs,mul_assoc,mul_inv_cancel,mul_one]
    have hb : b Sporadic.Mathieu.M22TripleCover.scalar =
        Sporadic.Mathieu.M22TripleCover.scalar := by
      change eB (a (eB.symm _)) = _
      rw [hfix,eB.apply_symm_apply]
    obtain ⟨y,hy⟩ := Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.inner_of_fixes_scalar b hb
    have ha : a = MulAut.conj (eB.symm y) := by
      apply (MulAut.congr eB).injective
      simpa only [MulAut.congr_conj,eB.apply_symm_apply] using hy
    have hm : t ∈ (MulAut.innerSubgroup B).comap (MulAut.conjNormal : HStar I →* MulAut B) :=
      ⟨eB.symm y,ha.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hm
    apply (sup_le le_rfl (show centralizer (B : Set (HStar I)) ≤ B from ?_)) hm
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := HStar I))
  · intro x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨z,hz,rfl⟩
    exact (congrArg Subtype.val (mem_center_iff.mp hz (⟨x,hx⟩ : B))).symm

theorem reduced_triple_mathieu_action_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let B := C.map q
    ∃ hU : IsElementaryAbelian 2 (F.UH I), let := hU
      ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        12 ≤ Module.finrank (ZMod 2) (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))) ∧
        fixedSpace a.representation B = ⊥ ∧
        (∀ t : HStar I, fixedCodim a.representation (zpowers t) ≠ 1) ∧
        ∃ A : Subgroup I,
          A ≤ (F.Ri L 1).subgroupOf I ∧ IsElementaryTwo (A.map q) ∧
          IsQuadratic a.representation (A.map q) ∧
          fixedCodim a.representation (A.map q) ≤ 2 * rank (A.map q) ∧
          A.map q ⊓ centralizer (B : Set (HStar I)) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  obtain ⟨hn,⟨eB⟩,_,hg,hpn,hz⟩ := reduced_triple_mathieu_star_structure_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hn
  obtain ⟨hU,a,hq,A,hAR,hA,hqa,hb,hf⟩ :=
    WholeResidualAssembly.GuardedSource.local_prime_supplement_quadratic_actor h hab structural previous I hI B hg
  let := hU
  have hd := Sporadic.Mathieu.M22TripleCover.faithful_finrank_ge_twelve eB
    (a.representation.comp B.subtype) (a.faithful.comp B.subtype_injective)
  refine ⟨hU,a,hq,hd,?_,WholeResidualAssembly.GuardedSource.local_normal_point_no_transvections h structural I
    (F.Li_one_le_of_mem_Hz hI) hpn a (by omega),A,hAR,hA,hqa,hb,hf⟩
  apply bot_unique
  intro v hv
  have hp := WholeResidualAssembly.GuardedSource.local_point_fixedSpace_eq_bot h structural I (F.Li_one_le_of_mem_Hz hI) hpn a
  rw [←hp]
  intro p
  have hb : (p : HStar I) ∈ B := by
    have hpZ : (p : HStar I) ∈ (center B).map B.subtype := by
      rw [←hz]
      exact p.property
    exact map_subtype_le _ hpZ
  exact hv ⟨p,hb⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt
