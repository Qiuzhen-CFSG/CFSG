module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalOffender
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Geometry

/-!
# The original critical offender from local structure

The exact section kernel puts the original point in the reciprocal
two-core. The common-line displacement bound on U ∩ Qα then gives the
fixed-codimension estimate on the actual U/V₁ section. This is the input
to the original G₂ orbit argument, without any recognition datum.
Source: AS 14.5.18(2) and F.9.16, pp.1018,324.
The structural source producer remains qt-d-1222-source; final
14.7.75 discharge remains with qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}


theorem point_le_reciprocal_core_of_kernel_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) : F.Vi 1 ≤ c.Qα := by
  let f := (MulAut.conj c.conjugator).toMonoidHom
  have hcancel : c.Uα.map f = F.U := by
    change (F.U.conjBy c.conjugator⁻¹).conjBy c.conjugator = F.U
    exact conjBy_inv' _ _
  have hcore : c.Qα.map f = F.H.pCoreIn 2 := by
    rw [CriticalPath.Qα,map_pCoreIn_of_injective 2 _ f (MulAut.conj c.conjugator).injective]
    change ((F.H.conjBy c.conjugator⁻¹).conjBy c.conjugator).pCoreIn 2 = _
    rw [conjBy_inv']
  have hA : (F.Vi 1).map f ≤ F.H := by
    have hh := map_mono (f:=f) ((F.le_seed 1).trans
      ((le_conjugateSpanBy V F.H).trans (G2Source.reciprocal_placement h c)))
    change (F.Vi 1).map f ≤ (F.H.conjBy c.conjugator⁻¹).conjBy c.conjugator at hh
    rwa [conjBy_inv'] at hh
  have hz : ⁅F.Vi 1,c.Uα⁆ = ⊥ := by
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact ((critical_le_Q_at h structural c).trans (Q_le_H F)).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  have hm : ⁅(F.Vi 1).map f,F.U⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map f) hz
    rwa [map_commutator,hcancel,Subgroup.map_bot] at hh
  have hle : (F.Vi 1).map f ≤ F.H.pCoreIn 2 := by
    intro a ha
    have hk : (⟨a,hA ha⟩ : F.H) ∈ ρ.ker := by
      apply (s.action_mem_ker_iff ⟨a,hA ha⟩).mpr
      intro u hu
      exact (hm.le.trans bot_le) (commutator_mem_commutator ha hu)
    rw [hkernel] at hk
    exact mem_map_of_mem F.H.subtype hk
  exact (map_le_map_iff_of_injective (f:=f) (MulAut.conj c.conjugator).injective).mp
    (hle.trans_eq hcore.symm)

private theorem line_image_dim_at
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (C : Subgroup G) (hC : Nat.card C = 2) :
    Module.finrank (ZMod 2) (s.imageSpace C) ≤ 1 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hDcard : Nat.card (s.imageSpace C) ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (by
          intro a b he
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : C => (z:G)) he)
    exact hm.trans (hs.trans hC.le)
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hDcard
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show 2 ≤ Module.finrank (ZMod 2) (s.imageSpace C) by omega)
  omega

theorem critical_fixedCodim_bounds_of_kernel_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) :
    fixedCodim ρ (c.Uα.subgroupOf F.H) ≤
      Nat.log 2 (Nat.card (star F c.Uα)) + Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ∧
      ∀ a : F.H, (a:G) ∈ c.Uα →
        Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  let : IsElementaryAbelian 2 c.Uα :=
    IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  let := IsElementaryAbelian.subgroupOf (p:=2) hAH
  let B := star F c.Uα
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (starMap F)
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  let τ := σ.comp B.subtype
  let D := F.U ⊓ c.Qα
  have hDH : c.Uα ≤ conjugate F.H c.conjugator := map_mono F.U_le_H
  have hDn : c.Uα ≤ normalizer (D:Set G) := by
    apply (le_inf (hAH.trans s.normalized) _).trans inf_normalizer_le_normalizer_inf
    exact hDH.trans ((conjugate F.H c.conjugator).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (conjugate F.H c.conjugator))))
  let P : Subrepresentation τ := {
    toSubmodule := s.imageSpace D
    apply_mem_toSubmodule := by
      rintro ⟨b,hb⟩ v hv
      obtain ⟨a,ha,rfl⟩ := hb
      obtain ⟨u,hu,rfl⟩ := (s.mem_imageSpace_iff D v).mp hv
      have he : τ ⟨starMap F a,mem_map_of_mem _ ha⟩ = ρ a :=
        congrArg (fun k : Representation (ZMod 2) F.H W => k a) hσ
      rw [he]
      refine (s.mem_imageSpace_iff D _).mpr ⟨⟨a*u*(a:G)⁻¹,
        (mem_normalizer_iff.mp (s.normalized a.property) u).mp u.property⟩,
        (mem_normalizer_iff.mp (hDn ha) u).mp hu,s.equivariant a u⟩ }
  have hline : Module.finrank (ZMod 2) (s.imageSpace c.Zα) ≤ 1 := by
    apply line_image_dim_at s c.Zα
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hc : ⁅c.Uα,D⁆ ≤ c.Zα := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_right le_rfl).trans
      (reciprocal_core_commutator_le_point h s c)
  have hdisp : ∀ b v, v ∈ P.toSubmodule → τ b v-v ∈ s.imageSpace c.Zα := by
    rintro ⟨b,hb⟩ v hv
    obtain ⟨a,ha,rfl⟩ := hb
    obtain ⟨u,hu,rfl⟩ := (s.mem_imageSpace_iff D v).mp hv
    have he : τ ⟨starMap F a,mem_map_of_mem _ ha⟩ = ρ a :=
      congrArg (fun k : Representation (ZMod 2) F.H W => k a) hσ
    rw [he]
    let z : F.U := (⟨a*u*(a:G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized a.property) u).mp u.property⟩ : F.U)*u⁻¹
    refine (s.mem_imageSpace_iff c.Zα _).mpr ⟨z,
      hc (commutator_mem_commutator ha hu),?_⟩
    rw [map_mul,map_inv]
    change (s.coordinates ⟨a*u*(a:G)⁻¹,_⟩).toAdd + -(s.coordinates u).toAdd = _
    rw [s.equivariant,sub_eq_add_neg]
  have hz : ∀ b z, z ∈ s.imageSpace c.Zα → τ b z=z := by
    rintro ⟨b,hb⟩ z hz
    obtain ⟨a,ha,rfl⟩ := hb
    have he : τ ⟨starMap F a,mem_map_of_mem _ ha⟩ = ρ a :=
      congrArg (fun k : Representation (ZMod 2) F.H W => k a) hσ
    rw [he]
    apply s.fixed_on_imageSpace_of_commutator_le c.Uα c.Zα _ a ha z hz
    have hZA : c.Zα ≤ c.Uα := map_mono ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    apply (commutator_mono le_rfl hZA).trans
    rw [commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative c.Uα)]
    exact bot_le
  have hbound := CommonCenter.fixedCodim_top_le_rank_add_codim τ P
    (s.imageSpace c.Zα) hline hdisp hz
  have hfixed : fixedCodim τ ⊤ = fixedCodim ρ (c.Uα.subgroupOf F.H) := by
    rw [←hσ]
    change Module.finrank (ZMod 2) (W ⧸ fixedSpace (σ.comp B.subtype) ⊤) =
      Module.finrank (ZMod 2) (W ⧸ fixedSpace (σ.comp (starMap F)) (c.Uα.subgroupOf F.H))
    rw [fixedSpace_comp_map, fixedSpace_comp_map, ←MonoidHom.range_eq_map, range_subtype]
    rfl
  rw [hfixed] at hbound
  have hPD : F.Vi 1 ≤ D := le_inf
    ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    (point_le_reciprocal_core_of_kernel_at h structural hkernel s c)
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F.U).to_quotient (D.subgroupOf F.U) |>.exists_card_eq
  have hindex : D.relIndex F.U = 2^n := hn
  have hdim := s.imageSpace_codimension_of_index D inf_le_left hPD n hindex
  have hquot := (s.imageSpace D).finrank_quotient_add_finrank
  have hcodim : Module.finrank (ZMod 2) (W ⧸ P.toSubmodule) = Nat.log 2 (D.relIndex F.U) := by
    rw [hindex,Nat.log_pow Nat.one_lt_two]
    change Module.finrank (ZMod 2) (W ⧸ s.imageSpace D) = n
    omega
  rw [hcodim] at hbound
  refine ⟨hbound,?_⟩
  intro a ha
  let b : B := ⟨starMap F a,mem_map_of_mem _ ha⟩
  let Z : Submodule (ZMod 2) P.toSubmodule :=
    (s.imageSpace c.Zα).comap P.toSubmodule.subtype
  have hZ : Module.finrank (ZMod 2) Z ≤ 1 := by
    have he : Module.finrank (ZMod 2) Z =
        Module.finrank (ZMod 2) (P.toSubmodule ⊓ s.imageSpace c.Zα : Submodule (ZMod 2) W) := by
      rw [←Submodule.finrank_map_subtype_eq,Submodule.map_comap_subtype]
    exact he.le.trans ((Submodule.finrank_mono inf_le_right).trans hline)
  have hd : fixedCodim P.toRepresentation (zpowers b) ≤ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    have hr : LinearMap.range (P.toRepresentation b - LinearMap.id) ≤ Z := by
      rintro _ ⟨v,rfl⟩
      exact hdisp b v v.property
    exact (Submodule.finrank_mono hr).trans hZ
  have hb := fixedCodim_le_subrepresentation_add_codim τ P (zpowers b)
  have he : τ b = ρ a := congrArg (fun k : Representation (ZMod 2) F.H W => k a) hσ
  rw [fixedCodim_zpowers_eq_displacement_rank,he,hcodim] at hb
  exact (hb.trans (Nat.add_le_add_right hd _)).trans_eq (Nat.add_comm _ _)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
