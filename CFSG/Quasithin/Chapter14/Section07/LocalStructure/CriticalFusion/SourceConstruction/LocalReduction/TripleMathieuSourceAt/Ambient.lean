module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuAmbient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt.Module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.StarQuotient

/-!
# Triple-Mathieu ambient at the original G,T

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
open Sporadic.Mathieu.M22TripleCover.Ambient
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension

theorem local_normal_point_sylow_centralizer_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let S := ((T : Subgroup G).subgroupOf I).map q
    let R := ((F.Ri L 1).subgroupOf I).map q
    R = S ⊓ centralizer ((((F.Li L 1).subgroupOf I).map q) : Set (HStar I)) ∧
      R.relIndex S = 2 := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  let X := ((F.Li L 1).subgroupOf I).map q
  let S := ((T : Subgroup G).subgroupOf I).map q
  let R := ((F.Ri L 1).subgroupOf I).map q
  let B' := (B.subgroupOf I).map q
  have hLI : F.Li L 1 ≤ I := le_sup_left.trans hBI
  have hTI : (T : Subgroup G) ≤ I := le_sup_right.trans hBI
  let hnX : X.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hR : R = B'.pCoreIn 2 := by
    have he : (B.subgroupOf I).pCoreIn 2 = (B.pCoreIn 2).subgroupOf I := by
      apply map_injective I.subtype_injective
      rw [map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
        map_subgroupOf_eq_of_le hBI,
        map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBI)]
    change ((B.pCoreIn 2).subgroupOf I).map q = _
    rw [←he,map_pCoreIn_of_ker_isPGroup q hk]
  have hc : Nat.card X = 3 := WholeResidualAssembly.GuardedSource.local_point_star_card_of_normal h structural I hLI hn
  have hthree : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hc)
  let SI : Sylow 2 I := T.subtype hTI
  let S' : Sylow 2 (HStar I) := SI.mapSurjective (QuotientGroup.mk'_surjective _)
  have hBS : B' = X ⊔ S := by
    dsimp [B',B,X,S]
    rw [subgroupOf_sup hLI hTI,Subgroup.map_sup]
  have hRS : R = S ⊓ centralizer (X : Set (HStar I)) := by
    rw [hR,hBS]
    exact core_join_odd_eq_sylow_centralizer X hthree S'
  refine ⟨hRS,?_⟩
  let f : B →* HStar I := q.comp (inclusion hBI)
  have hkf : IsPGroup 2 f.ker := hk.comap_of_injective _ (inclusion_injective hBI)
  have hf : f.range = B' := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨inclusion hBI b,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b.val,hb⟩,rfl⟩
  have hr := point_image_ratio_at h structural f hkf
  have hRc : Nat.card R = Nat.card (pCore 2 B') := by
    rw [hR]
    exact card_map_of_injective B'.subtype_injective
  rw [hf,←hRc] at hr
  have hBc : Nat.card B' = 3 * Nat.card S := by
    calc
      Nat.card B' = Nat.card (X ⊔ S : Subgroup (HStar I)) := congrArg (fun H : Subgroup (HStar I) => Nat.card H) hBS
      _ = Nat.card X * Nat.card S := card_sup_eq_mul_of_normalizes_of_disjoint X S
        le_normalizer_of_normal (hthree.disjoint_of_coprime
          (T.isPGroup'.comap_subtype.map q : IsPGroup 2 S) (by decide : Nat.Coprime 3 2))
      _ = 3 * Nat.card S := by rw [hc]
  rw [hBc] at hr
  have hindex := relIndex_mul_relIndex (⊥ : Subgroup (HStar I)) R S bot_le
    (hRS ▸ inf_le_left)
  simp only [relIndex_bot_left] at hindex
  have hpos := Nat.card_pos (α := R)
  nlinarith

theorem reduced_triple_mathieu_inner_sylow_at
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
    let S := ((T : Subgroup G).subgroupOf I).map q
    let R := ((F.Ri L 1).subgroupOf I).map q
    R = S ⊓ B ∧ R.relIndex S = 2 ∧
      ∃ P : Sylow 2 B, (P : Subgroup B).map B.subtype = R := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  obtain ⟨hn,_,_,_,hp,_⟩ := reduced_triple_mathieu_star_structure_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hn
  obtain ⟨hR,hi⟩ := local_normal_point_sylow_centralizer_at h structural I
    (sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)) hp
  rw [reduced_triple_mathieu_point_centralizer_at
    d h hab structural previous faithful earlier I hI C hC e hgen] at hR
  let S : Sylow 2 (HStar I) := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 I))
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal B
  exact ⟨hR,hi,P,hP.trans hR.symm⟩

theorem reduced_triple_mathieu_ambient_action_at
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
      ∃ (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
        (j : HStar I ≃* actionGroup)
        (E : Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)) ≃ₗ[ZMod 2]
          Sporadic.Mathieu.M22TripleCover.BinarySpace),
        (∀ g v, E (a.representation g v) = binaryAction (j g) (E v)) ∧
        B.map j.toMonoidHom = coverSubgroup ∧
        (((F.Li L 1).subgroupOf I).map q).map j.toMonoidHom = scalarSubgroup ∧
        Module.finrank (ZMod 2) (fixedSpace a.representation
          (((T : Subgroup G).subgroupOf I).map q)) = 1 ∧
        ∃ S : Sylow 2 actionGroup,
          (S : Subgroup actionGroup) = (((T : Subgroup G).subgroupOf I).map q).map j.toMonoidHom ∧
          (((F.Ri L 1).subgroupOf I).map q).map j.toMonoidHom =
            (S : Subgroup actionGroup) ⊓ coverSubgroup := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  obtain ⟨hn,_,_,_,_,hz⟩ := reduced_triple_mathieu_star_structure_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hn
  obtain ⟨hR,hi,_⟩ := reduced_triple_mathieu_inner_sylow_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  have hB : B ≠ ⊤ := by
    intro he
    change _ = _ ⊓ B at hR
    rw [he,inf_top_eq] at hR
    rw [hR,relIndex_self] at hi
    norm_num at hi
  obtain ⟨hU,a,_,_,eB,⟨E⟩,_⟩ := reduced_triple_mathieu_module_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hU
  let f := markedTripleAmbientHom a.representation B eB E
  have hinj : Function.Injective f := markedTripleAmbientHom_injective _ _ _ _ a.faithful
  have hsurj : Function.Surjective f := by
    rcases markedTripleAmbientHom_range_cases a.representation B eB E with he | he
    · exfalso
      apply hB
      apply top_unique
      intro g _
      exact (markedTripleAmbientHom_mem_cover_iff _ _ _ _ a.faithful g).mp
        (he ▸ (show f g ∈ f.range from ⟨g,rfl⟩))
    · exact MonoidHom.range_eq_top.mp he
  let j := MulEquiv.ofBijective f ⟨hinj,hsurj⟩
  have hBj : B.map j.toMonoidHom = coverSubgroup :=
    markedTripleAmbientHom_image _ _ _ _
  let SI : Sylow 2 (HStar I) := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 I))
  let S := SI.mapSurjective j.surjective
  refine ⟨hU,a,j,E.toLinearEquiv,markedTripleAmbientHom_intertwining _ _ _ _,hBj,?_,?_,?_⟩
  · rw [hz,map_map]
    have he : j.toMonoidHom.comp B.subtype = coverInclusion.comp eB.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact markedTripleAmbientHom_on_component a.representation B eB E x
    rw [he,←map_map]
    have hc : (center B).map eB.toMonoidHom = center Sporadic.Mathieu.M22TripleCover := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        rw [mem_center_iff]
        intro z
        obtain ⟨w,rfl⟩ := eB.surjective z
        change eB w * eB y = eB y * eB w
        exact (map_mul eB w y).symm.trans ((congrArg eB (mem_center_iff.mp hy w)).trans (map_mul eB y w))
      · intro hx
        refine ⟨eB.symm x,?_,eB.apply_symm_apply x⟩
        apply mem_center_iff.mpr
        intro y
        apply eB.injective
        simpa only [map_mul,eB.apply_symm_apply] using mem_center_iff.mp hx (eB y)
    rw [hc]
    rfl
  · have hm := fixedSpace_map_equivariant a.representation binaryAction j.toMonoidHom
      E.toLinearEquiv (markedTripleAmbientHom_intertwining a.representation B eB E)
      (((T : Subgroup G).subgroupOf I).map q)
    have hd := Sporadic.Mathieu.M22TripleCover.SylowFixed.sylow_fixed_finrank S
    change Module.finrank (ZMod 2) (fixedSpace binaryAction
      ((((T : Subgroup G).subgroupOf I).map q).map j.toMonoidHom)) = 1 at hd
    rw [←hm,E.toLinearEquiv.finrank_map_eq] at hd
    exact hd
  · refine ⟨S,rfl,?_⟩
    rw [hR]
    calc
      _ = (((T : Subgroup G).subgroupOf I).map q).map j.toMonoidHom ⊓ B.map j.toMonoidHom :=
        Subgroup.map_inf _ _ j.toMonoidHom (show Function.Injective j.toMonoidHom from j.injective)
      _ = (S : Subgroup actionGroup) ⊓ coverSubgroup := by rw [hBj]; rfl

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt
