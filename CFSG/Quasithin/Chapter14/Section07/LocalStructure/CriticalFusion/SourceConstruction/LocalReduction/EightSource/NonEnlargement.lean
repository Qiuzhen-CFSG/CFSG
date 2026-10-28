module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Movement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.NonEnlargement

/-!
# Non-enlargement of an original linear-four local

The actual component O²(I) embeds in O²(G₁). Its image modulo O₂(G₁) has
order divisible by 20160. Every row of 14.7.47 has order at most 20160,
except the linear-five row, which the invariant graph node excludes.
The component images therefore agree. The original full Sylow contains
the quotient kernel and supplements the larger component, giving I = G₁.

Source: Aschbacher–Smith 14.7.47–48, 14.7.51–52 and A.3.12,
printed pp.1064–1065 and 47–48.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- An original local with an intrinsic linear-four component quotient is
the full point group. All component rows and the five-dimensional exclusion
are supplied by the original source hypotheses. -/
theorem local_four_eq_full_point_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* SL(4, ZMod 2)) : I = F.H := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨D,hD,_,_⟩ := GuardedSource.local_exists_quasisimple_component
    d h hab structural previous faithful earlier F.H hH
  obtain ⟨hc,_,_⟩ := local_component_eq_residual_at d h hab structural previous faithful
    earlier source47 I hI C hC
  obtain ⟨hd,hdgen,_⟩ := local_component_eq_residual_at d h hab structural previous faithful
    earlier source47 F.H hH D hD
  let j : I →* F.H := inclusion hI.2.1
  let B := C.map j
  let q := QuotientGroup.mk' (pCore 2 F.H)
  let J := I.subgroupOf F.H
  have hBD : B ≤ D := by
    change C.map j ≤ D
    rw [←hc,←hd]
    exact map_pResidual_le 2 j
  let eB : C ≃* B := equivMapOfInjective C j (inclusion_injective hI.2.1)
  let eBQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  have hbcard : Nat.card (B ⧸ pCore 2 B) = 20160 := by
    rw [←Nat.card_congr eBQ.toEquiv,Nat.card_congr e.toEquiv,BinaryLinear.card_SL]
    norm_num [BinaryLinear.order,Fin.prod_univ_succ]
  have hDcard : Nat.card (D ⧸ pCore 2 D) ≤ 20160 := by
    rcases (source47 F.H hH D hD).2 with ⟨n,hn,hn',⟨eD⟩⟩ | ⟨n,hn,hn',⟨eD⟩⟩ | heD
    · have hn'' : n = 3 ∨ n = 4 ∨ n = 5 := by omega
      rcases hn'' with rfl | rfl | rfl
      · rw [Nat.card_congr eD.toEquiv,BinaryLinear.card_SL]
        norm_num [BinaryLinear.order,Fin.prod_univ_succ]
      · rw [Nat.card_congr eD.toEquiv,BinaryLinear.card_SL]
        norm_num [BinaryLinear.order,Fin.prod_univ_succ]
      · have hm := (local_linear_graph_movement_at d h hab structural previous faithful
          earlier source47 F.H hH D hD 5 (Or.inr rfl) eD).2
        exact (local_five_impossible_at d h hab structural previous faithful earlier
          source47 hm F.H hH D hD eD).elim
    · have hn'' : n = 5 ∨ n = 6 ∨ n = 7 := by omega
      rcases hn'' with rfl | rfl | rfl <;>
        rw [Nat.card_congr eD.toEquiv,nat_card_alternatingGroup,Nat.card_fin] <;> norm_num
    · obtain ⟨eD⟩ := heD
      rw [Nat.card_congr eD.toEquiv,Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]
      norm_num
  let f := q.subgroupMap B
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 F.H).comap B.subtype := by
      ext x
      change (⟨q x,_⟩ : B.map q) = 1 ↔ (x : F.H) ∈ pCore 2 F.H
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  have hdiv := f.pCoreQuotient_card_dvd_of_isPGroup_ker 2 hk
  have hbge : 20160 ≤ Nat.card (B.map q) := by
    rw [←hbcard]
    exact Nat.le_of_dvd Nat.card_pos hdiv
  have hdle : Nat.card (D.map q) ≤ 20160 := by
    rw [←Nat.card_congr (cComponentTwoCoreQuotientEquiv hD).toEquiv]
    exact hDcard
  have he : B.map q = D.map q :=
    eq_of_le_of_card_ge (map_mono hBD) (hdle.trans hbge)
  have hBJ : B ≤ J := by
    rintro _ ⟨c,_,rfl⟩
    exact c.property
  have hDJ : D.map q ≤ J.map q := he ▸ map_mono hBJ
  let S := T.subtype (F.sylow_le_of_mem_Hz hH)
  have hSJ : (S : Subgroup F.H) ≤ J := by
    intro t ht
    exact F.sylow_le_of_mem_Hz hI ht
  have hgen : D ⊔ (S : Subgroup F.H) = ⊤ := by
    apply map_injective F.H.subtype_injective
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hH),
      ←MonoidHom.range_eq_map,range_subtype]
    exact hdgen
  have hJq : J.map q = ⊤ := by
    apply top_unique
    rw [←map_top_of_surjective q (QuotientGroup.mk'_surjective _),←hgen,Subgroup.map_sup]
    exact sup_le hDJ (map_mono hSJ)
  have hcore : pCore 2 F.H ≤ J := (pCore_isPGroup.le_sylow_of_normal S).trans hSJ
  have hJ : J = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hJq
    rwa [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hcore,comap_top] at hh
  exact le_antisymm hI.2.1 (subgroupOf_eq_top.mp hJ)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
