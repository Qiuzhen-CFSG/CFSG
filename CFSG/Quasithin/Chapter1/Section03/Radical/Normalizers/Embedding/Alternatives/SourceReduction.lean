module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.NoncentralOddCore
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# The actual containing component in the case-ten source argument

The source radical obstruction excludes the noncentral-Fitting containing
branch by the proved A.3.12(21)–(22) producer. Thus the actual image of K
in N/O₂(N) is quasisimple. The full known-simple A.3.6 catalogue then gives
its simple or central three-cover model. All maps are the original source
quotients; no embedding-list premise is used.

Source: Aschbacher–Smith A.3.6, A.3.12(21)–(22), pp.43–48, and
Proposition 1.3.8, p.513. The remaining quasisimple target inspection is
separate from this containing-component reduction.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
universe u
variable {A : Type u} [Group A] [Finite A]

/-- A marked solvable normal two-perfect subgroup outside the containing
radical forces that containing C-component to be quasisimple. -/
theorem quasisimple_of_marked_radical_obstruction {κ : GroupClass.{u}} (hG : IsSQTK κ A) (hO : pCore 2 A = ⊥)
    (T : Sylow 2 A) {X B K : Subgroup A} [Group.IsPerfect B] [Group.IsSolvable X]
    (hlocal : B ∈ localCComponents T) (hK : K.IsCComponent)
    (hBK : B < K) (hXB : X ≤ B) (hXnormal : (X.subgroupOf B).Normal)
    (hXp : IsPPerfect 2 X) (hXrad : ¬ X ≤ (solvableRadical K).map K.subtype)
    (hB : ¬ IsQuasisimple (B ⧸ pCore 2 B)) (hcommon : A36Common K) :
    IsQuasisimple K := by
  have hf : fittingSubgroup K ≤ center K := by
    by_contra hn
    have he := SourceEmbeddings.embedding_of_noncentral_fitting hG hO T hlocal hK hBK.le hn
    obtain ⟨s,_,_,_,_,hm⟩ := case_ten_of_embedding hBK hXB hXnormal hXp hXrad hB hcommon he
    have hq : IsQuasisimple K := by
      rcases hm with ⟨F,_,_,_,⟨e⟩⟩ | ⟨F,_,_,_,⟨e⟩⟩
      · exact IsQuasisimple.of_mulEquiv e.symm
      · exact IsQuasisimple.of_mulEquiv e.symm
    exact NoncentralFitting.not_quasisimple_of_noncentral_fitting hn hq
  have hs : solvableRadical K = center K := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center K) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hK.perfect
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩

variable {G : Type u} [Group G] [Finite G]
/-- The original characteristic-normalizer image is quasisimple. -/
theorem actual_containing_image_quasisimple
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ K : Subgroup A,
      K.IsCComponent → A36Conclusion K)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (L : Subgroup G) (T : Sylow 2 G)
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (K : Subgroup G)
    (hK : K ∈ cComponentsIn (normalizer (C.map (radicalCore p L T).subtype : Set G)))
    (hYK : normalizerResidual L (radicalCore p L T) < K)
    (hY : normalizerResidual L (radicalCore p L T) ∈ Chapter1.L G T)
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hYq : ¬ IsQuasisimple (XiQuotient (normalizerResidual L (radicalCore p L T))))
    (hXrad : ¬ XiP p L ≤ (solvableRadical K).map K.subtype)
 :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    IsQuasisimple ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) := by
  let R := radicalCore p L T
  let N := normalizer (C.map R.subtype : Set G)
  let Y := normalizerResidual L R
  let X := XiP p L
  let q := QuotientGroup.mk' (pCore 2 N)
  let B := (Y.subgroupOf N).map q
  let Kbar := (K.subgroupOf N).map q
  let Xbar := (X.subgroupOf N).map q
  have hTN : (T : Subgroup G) ≤ N :=
    (t_le_normalizer_radicalCore p L T).trans
      (normalizer_le_normalizer_characteristic_image R C)
  have hYN : Y ≤ N := hYK.le.trans hK.1
  have hXN : X ≤ N := hXY.trans hYN
  have hYP : Group.IsPerfect (Y.subgroupOf N) := by
    let := mem_L_isPerfect hY
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hYN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hYN).symm.surjective
  let := hYP
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap (Y.subgroupOf N)) (q.subgroupMap_surjective _)
  have hXYN : Y.subgroupOf N ≤ normalizer (X.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hXN]
    exact comap_mono ((normalizerResidual_le L R).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L)))
  have hXnormal : (Xbar.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer
    ((map_mono (f := q) hXYN).trans ((X.subgroupOf N).le_normalizer_map q))
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsSolvable X := XiP_solvable p ho L
  let : Group.IsSolvable (X.subgroupOf N) := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe hXN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXN).symm.surjective
  let : Group.IsSolvable Xbar := Group.isSolvable_of_surjective
    (f := q.subgroupMap (X.subgroupOf N)) (q.subgroupMap_surjective _)
  have hXp : IsPPerfect 2 Xbar :=
    ((XiP_isPPerfect p L).of_surjective
      (subgroupOfEquivOfLe hXN).symm.toMonoidHom
      (subgroupOfEquivOfLe hXN).symm.surjective).of_surjective
        (q.subgroupMap (X.subgroupOf N)) (q.subgroupMap_surjective _)
  have hcommon : A36Common Kbar :=
    (proposition_1_2_1_four_earlier_conclusion hA36
      (characteristic_normalizer_quotient_sqtk hG p L T C hC) hK.2).2
  obtain ⟨hstrict, hnonq⟩ := actual_image_strict_and_not_quasisimple
    T hTN hY hK.1 hK.2 hYK hYq
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  let S : Sylow 2 N := T.subtype hTN
  have hYL : Y.subgroupOf N ∈ Chapter1.L N S := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (mem_LIn_iff_subgroupOf hTN hYN).mp ⟨hYN,hY⟩
  have hlocal : B ∈ localCComponents (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N)) : Subgroup _) := by
    simpa only [Sylow.coe_mapSurjective] using mem_L_map_twoCore_mem_localCComponents hYL
  exact quasisimple_of_marked_radical_obstruction (X := Xbar) (B := B) (K := Kbar)
    (characteristic_normalizer_quotient_sqtk hG p L T C hC)
    (pCore_quotient_pCore_eq_bot 2) _ hlocal (hK.2.map_quotient _)
    hstrict (map_mono (comap_mono hXY)) hXnormal hXp
    (actual_image_not_le_radical (hXY.trans hYK.le) hK.1 hXrad) hnonq hcommon


/-- The full known-simple containing catalogue on the literal source quotient. -/
theorem actual_containing_image_models_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (L : Subgroup G) (T : Sylow 2 G)
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (K : Subgroup G)
    (hK : K ∈ cComponentsIn (normalizer (C.map (radicalCore p L T).subtype : Set G)))
    (hYK : normalizerResidual L (radicalCore p L T) < K)
    (hY : normalizerResidual L (radicalCore p L T) ∈ Chapter1.L G T)
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hYq : ¬ IsQuasisimple (XiQuotient (normalizerResidual L (radicalCore p L T))))
    (hXrad : ¬ XiP p L ≤ (solvableRadical K).map K.subtype)
 :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let D := (K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
    IsQuasisimple D ∧ ((IsSimpleGroup D ∧ TheoremCModel D) ∨
      (Nonempty (center D ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel D)) := by
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let D := (K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
  have hq : IsQuasisimple D := actual_containing_image_quasisimple hG
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    p hp ho L T C hC K hK hYK hY hXY hYq hXrad
  let := hq
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  exact ⟨hq, SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    (characteristic_normalizer_quotient_sqtk hG p L T C hC)
    (pCore_quotient_pCore_eq_bot 2) (hK.2.map_quotient _)⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
