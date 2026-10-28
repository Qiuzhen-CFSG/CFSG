module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.Join.Ambient
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.Join.Transport
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.Join.Actors
public import Theory.GroupTheory.PCoreActionCardKernel

/-!
# Residual–radical generation from the full seven-letter moved action

The original omega-center commutator is normal in H. Its faithful ambient
action extends the supplied full star action, preserving the literal
subgroup inclusion and the natural-module coordinates. The six-dimensional
normalizer and the four-dimensional A7 normalizer show that KR already
fills the faithful actor. Its kernel is a two-group: the component image
has exactly the order of K/O2(K), and H/K is a two-group. This kernel lies
in O2(H), hence in R, proving H = KR. Normality of KR is never assumed.

The final application removes the join premise of block_types_of_join_eq
on the unchanged subgroups. The generated-parabolic assembly remains in
Reconstruction.Source.
Source: Aschbacher–Smith, C.2.7 and original14.6.10(5), pp.145–147 and1029.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- The full moved action forces generation by the original residual and radical. -/
theorem residual_join (h : Input KnownSimple.IsKnownSimple H R M K)
    (hK : K = (pResidual 2 H).map H.subtype)
    (hr : MSOddIndexRadical (R.subgroupOf H))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K)) :
    H = K ⊔ R := by
  let J := K ⊔ R
  let B := K.subgroupOf J
  let i : J →* H := inclusion h.join_le
  let U := ⁅starV K R,B⁆
  let W := U.map i
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (commutator_le_left _ _)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map i
  let : W.Normal := moved_normal h hK hr
  let Q := QuotientGroup.mk' (centralizer (W : Set H))
  have hQ : Function.Surjective Q := QuotientGroup.mk'_surjective _
  have hQk : Q.ker = centralizer (W : Set H) := QuotientGroup.ker_mk' _
  let ρ := NormalElementaryQuotient.representation W Q hQ hQk
  have hρ : Function.Injective ρ := NormalElementaryQuotient.representation_injective W Q hQ hQk
  have hKH : K.subgroupOf H = pResidual 2 H := by
    rw [hK]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  let : (K.subgroupOf H).Normal := hKH ▸ inferInstance
  have hBi : B.map i = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le h.component.1]
    exact map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)
  let : ((K.subgroupOf H).map Q).Normal := Normal.map inferInstance Q hQ
  have hmodel := (moved_wholeModule (starV K R) B
    (QuotientGroup.mk' (starKernel K R)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) m ((sevenStarEquiv h e).symm.trans e)).2
  have hfull : ((J.subgroupOf H).map Q) = ⊤ ∧
      Nat.card ((K.subgroupOf H).map Q) = Nat.card (alternatingGroup (Fin 7)) := by
    rcases hmodel with ⟨q,hq,hk,hBq,E,he⟩ | ⟨q,hq,hk,hBq,hd⟩
    · let f := actorMap i (inclusion_injective h.join_le) U q hq hk Q hQk
      have hf := actorMap_injective i (inclusion_injective h.join_le) U q hq hk Q hQk
      have him : (alternatingGroup (Fin 7)).map f = (K.subgroupOf H).map Q := by
        rw [←hBq,actorMap_image,hBi]
      let : ((alternatingGroup (Fin 7)).map f).Normal := him ▸ inferInstance
      let F := embeddedLinearEquiv i (inclusion_injective h.join_le) U
      have hinter (s) (v : Additive U) :=
        embedded_intertwines i (inclusion_injective h.join_le) U q hq hk Q hQk hQ s v
      have hs : Function.Surjective f := natural_actor_surjective ρ hρ f hf
        (F.symm.trans E) (by
          intro s v
          obtain ⟨w,rfl⟩ := F.surjective v
          change E (F.symm (ρ (f s) (F w))) = _
          rw [←hinter,F.symm_apply_apply]
          simpa only [LinearEquiv.trans_apply,F.symm_apply_apply] using he s w)
      refine ⟨?_,?_⟩
      · apply top_unique
        intro d _
        obtain ⟨s,rfl⟩ := hs d
        obtain ⟨a,rfl⟩ := hq s
        exact ⟨i a,a.property,actorMap_apply i (inclusion_injective h.join_le) U q hq hk Q hQk a |>.symm⟩
      · rw [←him,card_map_of_injective hf]
    · let f := actorMap i (inclusion_injective h.join_le) U q hq hk Q hQk
      have hf := actorMap_injective i (inclusion_injective h.join_le) U q hq hk Q hQk
      have him : f.range = (K.subgroupOf H).map Q := by
        rw [MonoidHom.range_eq_map,←hBq,actorMap_image,hBi]
      let : f.range.Normal := him ▸ inferInstance
      let F := embeddedLinearEquiv i (inclusion_injective h.join_le) U
      have hdW : Module.finrank (ZMod 2) (Additive W) = 4 := F.finrank_eq.symm.trans hd
      have hs : Function.Surjective f := exceptional_actor_surjective ρ hρ hdW f hf
      refine ⟨?_,?_⟩
      · apply top_unique
        intro d _
        obtain ⟨s,rfl⟩ := hs d
        obtain ⟨a,rfl⟩ := hq s
        exact ⟨i a,a.property,actorMap_apply i (inclusion_injective h.join_le) U q hq hk Q hQk a |>.symm⟩
      · rw [←him,←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  have hquot : IsPGroup 2 (H ⧸ K.subgroupOf H) := by
    exact (isPGroup_quotient_pResidual (G := H) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hKH.symm)
  let eKH : K.subgroupOf H ≃* K := subgroupOfEquivOfLe h.component.1
  have hc : Nat.card ((K.subgroupOf H).map Q) = Nat.card ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) := by
    rw [hfull.2, Nat.card_congr (QuotientGroup.congr _ _ eKH (pCore_map_iso 2 eKH)).toEquiv,
      Nat.card_congr e.toEquiv]
  have hker : IsPGroup 2 Q.ker := Q.isPGroup_ker_of_card_image_eq_core_quotient
    (K.subgroupOf H) hquot hc
  have hkerR : Q.ker ≤ R.subgroupOf H := (le_sSup ⟨inferInstance,hker⟩ : Q.ker ≤ pCore 2 H).trans hr.twoCore_le
  apply le_antisymm ?_ h.join_le
  intro a ha
  have hm : Q ⟨a,ha⟩ ∈ (J.subgroupOf H).map Q := hfull.1 ▸ mem_top _
  obtain ⟨j,hj,he⟩ := hm
  have hk : (⟨a,ha⟩ : H) * j⁻¹ ∈ Q.ker := by
    change Q _ = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hjk : a * (j : G)⁻¹ ∈ J := mem_sup_right (hkerR hk)
  have hh := J.mul_mem hjk hj
  change (a * (j : G)⁻¹) * (j : G) ∈ J at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join

namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The residual-join contract, with no additional source or action premises. -/
theorem residualJoinInput : ResidualJoinInput (G := G) := by
  intro H K R M h hK hr e m
  exact Join.residual_join h hK hr e m

/-- Discharge the join hypothesis for the same component, radical and ambient group. -/
theorem block_types_of_residual_join {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hK : K = (pResidual 2 H).map H.subtype)
    (hr : MSOddIndexRadical (R.subgroupOf H))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (P : Sylow 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K.subgroupOf H, ∃ t ∈ (P : Subgroup H), k*t=g)
    (hno : ∀ D : Subgroup (ChapterB.baumann (P : Subgroup H)),
      D.Characteristic → D ≠ ⊥ → ¬ (D.map (ChapterB.baumann (P : Subgroup H)).subtype).Normal) :
    IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K :=
  block_types_of_join_eq h (residualJoinInput H K R M h hK hr e m) e P hprod hno

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
