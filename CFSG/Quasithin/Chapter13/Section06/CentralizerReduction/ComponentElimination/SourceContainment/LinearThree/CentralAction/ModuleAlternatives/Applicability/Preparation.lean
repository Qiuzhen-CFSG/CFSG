module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Maximum

public import Theory.Representation.BinaryOffender.Stability

/-!
# Preparing the literal plus action for the module classifiers

The Sylow subgroup fixes the seed z. Consequently the preimage of the
normal two-core in the faithful plus quotient fixes every conjugate of z,
so the quotient has trivial two-core. Characteristic two puts U_v inside
its core's elementary omega-center, and W_K inherits elementary structure.

The maximum-elementary Thompson image lies in the offender subgroup on
W_K. Transporting the X_z commutator identity then puts K+ in that normal
subgroup; the full plus actor is never identified with its offender group.
The SQTK cover is the original subgroup K₋L_vT_v of C_G(v), with the
literal action kernel and quotient. All statements retain the original
class 𝒦.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.2.5 and
B.2.14, printed pp.76–78; the paragraph preceding 13.6.14, p.929;
the application of B.5.1 and B.5.6 in 13.6.20, p.931.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

theorem wk_elementary (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    IsElementaryAbelian 2 (WK K L T z v) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv v)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  exact IsElementaryAbelian.of_le
    ((WK_le_Uv K L T z v hK).trans (Uv_le_coreOmega T z v hSylow hz hf))

omit [Finite G] in
theorem plusImage_K_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    (plusImage K L T z v hL hz K).Normal := by
  have h := starImage_Kminus_normal_in_actor K L T z v hK
  rw [Kminus_eq_of_invariant K T v hn] at h
  have hm := h.map (starToPlus K L T z v hK.1.1 hL hz)
    (starToPlus_surjective K L T z v hK.1.1 hL hz)
  rwa [starToPlus_image K L T z v hK.1.1 hL hz K (K_le_plusActor K L T v)] at hm

theorem plus_twoCore_eq_bot (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    pCore 2 (Gplus K L T z v hL hz) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := plusActor K L T v
  let f := plusMk K L T z v hL hz
  let Q := pCore 2 (Gplus K L T z v hL hz)
  let N := (Q.comap f).map A.subtype
  obtain ⟨P, hP⟩ := hSylow.restrict
    (show Tv T v ≤ A from le_sup_right) (plusActor_le_Gv K L T v hK)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  let Pplus := P.mapSurjective hf
  have hQP : Q ≤ (Pplus : Subgroup _) := pCore_isPGroup.le_sylow_of_normal Pplus
  have hNA : A ≤ normalizer (N : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    change (((Q.comap f).map A.subtype).comap A.subtype).Normal
    rw [comap_map_eq_self_of_injective A.subtype_injective]
    infer_instance
  have hNz : N ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    rintro g ⟨x, hx, rfl⟩
    obtain ⟨t, ht, he⟩ := hQP hx
    have htT : (t : G) ∈ Tv T v := hP ▸ mem_map_of_mem A.subtype ht
    have hez := congrArg (fun a : Gplus K L T z v hL hz =>
      ((plusAction K L T z v hL hz a
        ⟨z, le_conjugateSpanBy _ _ (mem_zpowers z)⟩ : WK K L T z v) : G)) he
    change (t : G) * z * (t : G)⁻¹ = (x : G) * z * (x : G)⁻¹ at hez
    have htfix : (t : G) * z * (t : G)⁻¹ = z := by
      rw [mem_centralizer_singleton_iff.mp (hz htT)]
      simp [mul_assoc]
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (hez.symm.trans htfix))
  have hNW : N ≤ centralizer (WK K L T z v : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ _ _
      ((show Kminus K T v ⊔ Lv L v ≤ A from le_sup_left).trans hNA) hNz
  apply _root_.eq_bot_iff.mpr
  intro q hq
  obtain ⟨x, rfl⟩ := hf q
  change f x = 1
  have hx : x ∈ f.ker := by
    rw [show f.ker = (centralizer (WK K L T z v : Set G)).subgroupOf A from
      plusMk_ker K L T z v hL hz]
    exact hNW (mem_map_of_mem A.subtype hq)
  exact hx

private theorem offender_le_of_linearEquiv {D U W : Type*} [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D U) (σ : Representation (ZMod 2) D W)
    (e : U ≃ₗ[ZMod 2] W) (he : ∀ g u, e (ρ g u) = σ g (e u)) :
    offenderSubgroup ρ ≤ offenderSubgroup σ := by
  have hw (B : Subgroup D) : weight ρ B = weight σ B := by
    have h := fixedSpace_map_equivariant ρ σ (MonoidHom.id D) e he B
    rw [Subgroup.map_id] at h
    unfold weight
    rw [← h, LinearEquiv.finrank_map_eq]
  unfold offenderSubgroup generatedBy
  refine iSup_le fun B => iSup_le fun hB => ?_
  have hb : IsBestOffender σ B := ⟨hB.1.1, fun C hC => by
    rw [← hw C, ← hw B]
    exact hB.1.2 C hC⟩
  exact le_iSup_of_le B (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)

theorem thompson_plus_le_offenders (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)] (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) ≤
      offenderSubgroup (wkRepresentation K L T z v hL hz) := by
  let A := plusActor K L T v
  let W := (WK K L T z v).subgroupOf A
  have hWA : WK K L T z v ≤ A := conjugateSpanBy_le
    (zpowers_le.mpr ((show Tv T v ≤ A from le_sup_right) hzT))
    ((show Kminus K T v ⊔ Lv L v ≤ A from le_sup_left).trans A.le_normalizer)
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (plusActor_normalizes_WK K L T z v hL hz)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWA
  let f := plusMk K L T z v hL hz
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hk : f.ker = centralizer (W : Set A) := by
    rw [show f.ker = (centralizer (WK K L T z v : Set G)).subgroupOf A from
      plusMk_ker K L T z v hL hz]
    ext a
    constructor
    · intro ha w hw
      exact Subtype.ext (ha w hw)
    · intro ha w hw
      exact congrArg Subtype.val (ha ⟨w, hWA hw⟩ hw)
  let τ := NormalElementaryQuotient.representation W f hf hk
  let e : Additive W ≃ₗ[ZMod 2] Additive (WK K L T z v) :=
    { (subgroupOfEquivOfLe hWA).toAdditive with
      map_smul' := ZMod.map_smul (subgroupOfEquivOfLe hWA).toMonoidHom.toAdditive }
  have he : ∀ g w, e (τ g w) = wkRepresentation K L T z v hL hz g (e w) := by
    intro g w
    obtain ⟨a, rfl⟩ := hf g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (NormalElementaryQuotient.representation_apply W f hf hk a w)).trans
      (wkRepresentation_apply K L T z v hL hz a (e w)).symm
  obtain ⟨P, hP⟩ := hSylow.restrict
    (show Tv T v ≤ A from le_sup_right) (plusActor_le_Gv K L T v hK)
  have hJ : (elementaryAbelianMaxJ (Tv T v)).subgroupOf A =
      elementaryAbelianMaxJ (P : Subgroup A) := by
    rw [← hP, elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hj := CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.thompson_image_le_internal_offenderSubgroup
    (P : Subgroup A) W ((IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P) f hf hk
  change ((elementaryAbelianMaxJ (Tv T v)).subgroupOf A).map f ≤ _
  rw [hJ]
  exact hj.trans (offender_le_of_linearEquiv τ _ e he)

omit [Finite G] in
theorem component_plus_commutator (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))⁆ =
        plusImage K L T z v hL hz K := by
  let A := starImage z v (plusActor K L T v)
  let C := starImage z v K
  let J := starImage z v (elementaryAbelianMaxJ (Tv T v))
  have hJA : elementaryAbelianMaxJ (Tv T v) ≤ plusActor K L T v :=
    (sSup_le fun _ h => h.1).trans le_sup_right
  have hCA : C ≤ A := map_mono (comap_mono (K_le_plusActor K L T v))
  have hJAs : J ≤ A := map_mono (comap_mono hJA)
  have hc : ⁅C, J⁆ = C := (invariant_component_consequences K L T z v hK hn).1.1.2.2.2
  have hr : ⁅C.subgroupOf A, J.subgroupOf A⁆ = C.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hCA,
      map_subgroupOf_eq_of_le hJAs, hc]
  have hm := congrArg (map (starToPlus K L T z v hK.1.1 hL hz)) hr
  rw [map_commutator] at hm
  simpa only [C, J, A,
    starToPlus_image K L T z v hK.1.1 hL hz K (K_le_plusActor K L T v),
    starToPlus_image K L T z v hK.1.1 hL hz (elementaryAbelianMaxJ (Tv T v)) hJA] using hm

theorem component_plus_le_offenders (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    plusImage K L T z v hL hz K ≤ offenderSubgroup (wkRepresentation K L T z v hL hz) := by
  let ρ := wkRepresentation K L T z v hL hz
  let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
  rw [← component_plus_commutator K L T z v hL hz hK hn]
  exact (commutator_mono le_rfl
    (thompson_plus_le_offenders K L T z v hK.1.1 hL hz hzT hSylow)).trans
      (commutator_le_right _ _)

theorem plus_sqtk_quotient {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Nonempty (ChapterB.SourceInduction.SQTKQuotient 𝒦 (Gplus K L T z v hL hz)) := by
  have hA : IsSQTK 𝒦 (plusActor K L T v) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (plusActor_le_Gv K L T v hK))).mp
      ((hG.involution_centralizer_sqtk hv).subgroup ((plusActor K L T v).subgroupOf (Gv v)))
  exact ⟨{ Cover := plusActor K L T v
           kernel := (plusConjugation K L T z v hL hz).ker
           sqtk := hA
           equiv := MulEquiv.refl _ }⟩

/-- All preparation hypotheses for the actual plus representation, using only
local source data; the classifiers themselves are not used. -/
theorem classifierApplicability_of_local {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    ClassifierApplicability 𝒦 (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  exact ⟨Module.Finite.of_finite, wkRepresentation_faithful K L T z v hL hz,
    plus_twoCore_eq_bot K L T z v hK.1.1 hL hz hSylow,
    plusImage_K_normal K L T z v hL hz hK hn,
    component_plus_le_offenders K L T z v hL hz
      ((mem_omegaOneCenterAmbient_iff (Tv T v) z).mp hzOmega).1 hSylow hK hn,
    plus_sqtk_quotient hG K L T z v hv hK.1.1 hL hz⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
