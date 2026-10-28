module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuRankTwo
public import Theory.Representation.Mathieu.M22James.MinimumFaithfulDegree

/-!
# The literal reduced triple-Mathieu action

For the original reduction J = C T, the actual image of C in J/O₂(J) is
isomorphic to the triple Mathieu cover and is the whole generalized Fitting
subgroup. The point cubic is its center. An automorphism fixing this center
is inner, so its full centralizer in J/O₂(J) is precisely the component image.

The original quadratic action on U_J/V₁ is faithful. Detecting the cubic
center on a chief factor proves that this whole section has dimension at
least twelve. Point normality then excludes transvections and constructs a
strict reciprocal endpoint on the same action. The last theorem applies
these results to the original point component and its constructed C T.

The upper dimension bound, irreducibility and model recognition, and the
Sylow fixed-line/solvable-overgroup contradiction remain separate steps.
Source: Aschbacher–Smith 14.7.36, printed p.1059, using 14.7.5, F.9.16–18
and H.12.1; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section06.OddCriticalPair.Selection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal component image is the entire generalized Fitting subgroup
of the reduced star group, with the original point center retained. -/
theorem reduced_triple_mathieu_star_structure
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨hn,_,hz,hpn,_,_,_⟩ := local_triple_mathieu_central_point
    d h hab structural previous faithful earlier I hI C hC e
  let := hn
  let hnB : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple B :=
    (local_component_star_isComponent h hab structural previous faithful I hI C hC).2
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

/-- In the reduced local, the point cubic's full centralizer is exactly the
triple-cover component image. Scalar-fixing automorphisms are inner, and
self-centralization of F* removes the remaining centralizer factor. -/
theorem reduced_triple_mathieu_point_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    centralizer ((((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) :
      Set (HStar I)) = C.map (QuotientGroup.mk' (pCore 2 I)) := by
  let B := C.map (QuotientGroup.mk' (pCore 2 I))
  obtain ⟨hn,⟨eB⟩,hfit,_,_,hz⟩ := reduced_triple_mathieu_star_structure
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

/-- Construct the original faithful quadratic action and discharge its
minimum-degree, fixed-space and no-transvection premises. -/
theorem reduced_triple_mathieu_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨hn,⟨eB⟩,_,hg,hpn,hz⟩ := reduced_triple_mathieu_star_structure
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hn
  obtain ⟨hU,a,hq,A,hAR,hA,hqa,hb,hf⟩ :=
    local_prime_supplement_quadratic_actor h hab structural previous I hI B hg
  let := hU
  have hd := Sporadic.Mathieu.M22TripleCover.faithful_finrank_ge_twelve eB
    (a.representation.comp B.subtype) (a.faithful.comp B.subtype_injective)
  refine ⟨hU,a,hq,hd,?_,local_normal_point_no_transvections h structural I
    (F.Li_one_le_of_mem_Hz hI) hpn a (by omega),A,hAR,hA,hqa,hb,hf⟩
  apply bot_unique
  intro v hv
  have hp := local_point_fixedSpace_eq_bot h structural I (F.Li_one_le_of_mem_Hz hI) hpn a
  rw [←hp]
  intro p
  have hb : (p : HStar I) ∈ B := by
    have hpZ : (p : HStar I) ∈ (center B).map B.subtype := by
      rw [←hz]
      exact p.property
    exact map_subtype_le _ hpZ
  exact hv ⟨p,hb⟩

/-- Apply the actual reduced action and point-centralizer identity to the
original component, and construct its strict reciprocal endpoint. -/
theorem original_triple_mathieu_selected_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) :
    let D := C.map F.H.subtype
    let J := D ⊔ (T : Subgroup G)
    let B := (D.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
    J ≤ F.H ∧ ∃ hJ : J ∈ F.Hz L (normalizer (L : Set G)),
      B.Normal ∧ Nonempty (B ≃* Sporadic.Mathieu.M22TripleCover) ∧
      generalizedFitting (HStar J) = B ∧
      centralizer ((((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) :
        Set (HStar J)) = B ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH J), let := hU
        ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
          quadraticRatio a.representation ≤ 2 ∧
          12 ≤ Module.finrank (ZMod 2) (Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J))) ∧
          fixedSpace a.representation B = ⊥ ∧
          (∀ t : HStar J, fixedCodim a.representation (zpowers t) ≠ 1) ∧
          let hf := local_f9_hypothesis h hab structural previous J hJ
          letI : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L J).UH :=
            inferInstanceAs (IsElementaryAbelian 2 (F.UH J))
          Nonempty (SelectedQuadraticEndpoint hf a) := by
  let D := C.map F.H.subtype
  let J := D ⊔ (T : Subgroup G)
  obtain ⟨hJH,hJ,hDJ,_,_,_,_,hpn,_,_,_⟩ :=
    original_triple_mathieu_reduced_residual d h hab structural previous faithful earlier C hC e
  let b := equivMapOfInjective C F.H.subtype F.H.subtype_injective
  let eD := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans e
  let c := subgroupOfEquivOfLe (show D ≤ J from le_sup_left)
  let eJ := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans eD
  have hg : D.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show D ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  obtain ⟨hn,he,hfit,_,_,_⟩ := reduced_triple_mathieu_star_structure
    d h hab structural previous faithful earlier J hJ (D.subgroupOf J) hDJ eJ hg
  obtain ⟨hU,a,hq,hd,hfix,hnt,_⟩ := reduced_triple_mathieu_action
    d h hab structural previous faithful earlier J hJ (D.subgroupOf J) hDJ eJ hg
  let := hU
  have hz := reduced_triple_mathieu_point_centralizer
    d h hab structural previous faithful earlier J hJ (D.subgroupOf J) hDJ eJ hg
  exact ⟨hJH,hJ,hn,he,hfit,hz,hU,a,hq,hd,hfix,hnt,
    local_normal_point_selected_endpoint h hab structural previous J hJ hpn a (by omega)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
