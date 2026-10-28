module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientNaturalSeedThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSeedSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianOne
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientInvariantSubgroup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearLayer
public import Theory.Representation.BinaryAlternatingFiveFixedPoint.Coordinates
public import Theory.Representation.AlternatingFive.AmplifiedDeleted.CubicMultiplicity
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubledSelection

/-!
# The stationary degree-two deleted A₅ row on the original layer

The deleted type has a canonical complement preserved by the full original
quotient action. A nonzero complement is an actual noncentral invariant
subgroup, hence admits original stationary seed selection. Natural seeds
fill the entire original layer, whereas deleted A₅ seeds embed into the
complementary type span. Both alternatives contradict the complement.
The original cubic bound then limits the whole deleted multiplicity to two.

Source: Aschbacher--Smith 5.1.3 and 6.1.4, pp.630--631,664--665; I.1.6.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryPermutation
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem a5_model_core_embedding
    {G : Type*} [Group G] {L W U : Subgroup G} [IsElementaryAbelian 2 W]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 5)) (Additive W))
    (hτ : ∀ (l : L) (v : Additive W),
      ((τ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : G) =
        (l : G) * (v.toMul : G) * (l : G)⁻¹)
    (hUW : U ≤ W) (hm : IsConjugationModel L U a5Module) :
    ∃ f : (alternatingCoreRepresentation (Fin 5)).IntertwiningMap τ,
      Function.Injective f ∧ ∀ v, ((f v).toMul : G) ∈ U := by
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUW
  obtain ⟨e',m,hm⟩ := hm
  let a : MulAut (alternatingGroup (Fin 5)) := e.symm.trans e'
  obtain ⟨c,hc⟩ := BinaryAlternatingFiveFixedPoint.core_twist a
  let d := coreEquivNatural (Fin 5) (by decide)
  let mc : Additive U ≃ₗ[ZMod 2] natural (Fin 5) :=
    m.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  let j : Additive U →ₗ[ZMod 2] Additive W :=
    (inclusion hUW).toAdditive.toZModLinearMap 2
  let F := j.comp (mc.symm.toLinearMap.comp (c.trans d).toLinearMap)
  have hd (g : alternatingGroup (Fin 5)) (v : core (Fin 5)) :
      d (alternatingCoreRepresentation (Fin 5) g v) = a5Module g (d v) :=
    coreEquivNatural_equivariant (Fin 5) (by decide) g.val v
  have hF (g : alternatingGroup (Fin 5)) (v : core (Fin 5)) :
      F (alternatingCoreRepresentation (Fin 5) g v) = τ g (F v) := by
    obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    dsimp only [Function.comp_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hτ]
    change (m.symm (Multiplicative.ofAdd (d (c
      (alternatingCoreRepresentation (Fin 5) (e (QuotientGroup.mk' (pCore 2 L) l)) v)))) : G) =
      (l : G) * (m.symm (Multiplicative.ofAdd (d (c v))) : G) * (l : G)⁻¹
    rw [hc,hd]
    have ha : a (e (QuotientGroup.mk' (pCore 2 L) l)) =
        e' (QuotientGroup.mk' (pCore 2 L) l) := by
      change e' (e.symm (e _)) = _
      rw [e.symm_apply_apply]
    rw [ha]
    simpa only [m.apply_symm_apply,toAdd_ofAdd] using
      hm l (m.symm (Multiplicative.ofAdd (d (c v))))
  let f : (alternatingCoreRepresentation (Fin 5)).IntertwiningMap τ := {
    toLinearMap := F
    isIntertwining' := fun g => LinearMap.ext (hF g) }
  have hj : Function.Injective j := by
    intro u v he
    apply Additive.toMul.injective
    exact inclusion_injective hUW (congrArg Additive.toMul he)
  refine ⟨f,hj.comp (mc.symm.injective.comp (c.trans d).injective),?_⟩
  intro v
  exact (mc.symm (d (c v))).toMul.property

private theorem marked_a5_covariance
    {Q X : Type*} [Group Q] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) Q X) (K : Subgroup Q) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 5)) (x : Q) :
    ∃ a : MulAut (alternatingGroup (Fin 5)), ∀ g v,
      ρ x (ρ (e.symm g : Q) v) = ρ (e.symm (a g) : Q) (ρ x v) := by
  let a := (MulAut.congr e) (MulAut.conjNormal x)
  refine ⟨a,?_⟩
  intro g v
  have he : (e.symm (a g) : Q) = x * (e.symm g : Q) * x⁻¹ := by
    change (e.symm (e (MulAut.conjNormal x (e.symm g))) : Q) = _
    rw [e.symm_apply_apply]
    rfl
  rw [he]
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]

private theorem marked_a5_reject_stable
    {Q X : Type*} [Group Q] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) Q X) (K : Subgroup Q) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 5)) (x : Q) (v : X)
    (hv : v ∈ typeReject ((ρ.comp K.subtype).comp e.symm.toMonoidHom)
      (alternatingCoreRepresentation (Fin 5))) :
    ρ x v ∈ typeReject ((ρ.comp K.subtype).comp e.symm.toMonoidHom)
      (alternatingCoreRepresentation (Fin 5)) := by
  obtain ⟨a,ha⟩ := marked_a5_covariance ρ K e x
  obtain ⟨c,hc⟩ := BinaryAlternatingFiveFixedPoint.core_twist a
  exact typeReject_stable_of_covariance _ _ (ρ x) a c ha hc v hv

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V U : Subgroup G} {n : ℕ}

/-- In the original stationary degree-two branch, no deleted A₅ seed can
lie in the actual moved layer. The whole deleted row is constructed and
then excluded by the original hypothesis. -/
theorem original_stationary_a5_seed_false
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hj : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (layer L V : Set G))
    (hn : n = 2) (hUW : U ≤ layer L V)
    (hm : IsConjugationModel L U a5Module) : False := by
  let W := layer L V
  have hi := (h.rankOneInput hout).commutator_input
  let := hi.reduced.2.1
  let J := L ⊔ (T : Subgroup G)
  let W₀ := W.subgroupOf J
  let B := L.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := hi.reduced_internal.normal
  let := hi.reduced_internal.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer hi.sylow_normalizes)
  let Q := J ⧸ pCore 2 J
  let q : J →* Q := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (W₀ : Set J) :=
    (QuotientGroup.ker_mk' _).trans hi.reduced_centralizer_eq_twoCore.symm
  let ρ₀ := NormalElementaryQuotient.representation W₀ q hq hk
  let wW : W₀ ≃* W := subgroupOfEquivOfLe hi.reduced.1
  let C : Additive W₀ ≃ₗ[ZMod 2] Additive W :=
    wW.toAdditive.toLinearEquiv (ZMod.map_smul _)
  let ρ : Representation (ZMod 2) Q (Additive W) :=
    C.conjRingEquiv.toMonoidHom.comp ρ₀
  have hρ (g : J) (v : Additive W) :
      ((ρ (q g) v).toMul : G) = (g : G) * (v.toMul : G) * (g : G)⁻¹ := by
    change (((ρ₀ (q g) (C.symm v)).toMul : J) : G) = _
    rw [NormalElementaryQuotient.representation_apply]
    have he : (((C.symm v).toMul : J) : G) = (v.toMul : G) :=
      congrArg (fun z : Additive W => (z.toMul : G)) (C.apply_symm_apply v)
    change (g : G) * (((C.symm v).toMul : J) : G) * (g : G)⁻¹ = _
    rw [he]
  have hcubic : cubicRatio ρ ≤ 2 := by
    apply cubicRatio_le_nat_of_equivariant ρ₀ ρ (MonoidHom.id Q) Function.injective_id C
      (fun a v => by
        change C (ρ₀ a v) = C (ρ₀ a (C.symm (C v)))
        rw [C.symm_apply_apply]) 2
    exact hi.core_quotient_cubicRatio_le_two
  obtain ⟨e0,f0,hf0⟩ := hm
  let K := B.map q
  let : K.Normal := (inferInstance : B.Normal).map q hq
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eK₀ : K ≃* (L ⧸ pCore 2 L) :=
    (coreQuotientEquivImage 2 B).symm.trans
      (QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb))
  let eK : K ≃* alternatingGroup (Fin 5) := eK₀.trans e0
  have heK (b : B) : eK (q.subgroupMap B b) =
      e0 (QuotientGroup.mk' (pCore 2 L) (eb b)) := by
    change e0 (QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)
      ((coreQuotientEquivImage 2 B).symm (q.subgroupMap B b))) = _
    have heq : coreQuotientEquivImage 2 B (QuotientGroup.mk' (pCore 2 B) b) =
        q.subgroupMap B b := by
      apply Subtype.ext
      exact coreQuotientEquivImage_apply_mk 2 B b
    rw [←heq,MulEquiv.symm_apply_apply]
    rfl
  let τ := (ρ.comp K.subtype).comp eK.symm.toMonoidHom
  have hτ (l : L) (v : Additive W) :
      ((τ (e0 (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : G) =
        (l : G) * (v.toMul : G) * (l : G)⁻¹ := by
    have he := heK (eb.symm l)
    rw [eb.apply_symm_apply] at he
    rw [←he]
    change ((ρ (eK.symm (eK (q.subgroupMap B (eb.symm l))) : Q) v).toMul : G) = _
    rw [eK.symm_apply_apply]
    exact hρ (eb.symm l).val v
  let R₀ := typeReject τ (alternatingCoreRepresentation (Fin 5))
  let R := ambientSubspace W R₀.toSubmodule
  have hRW : R ≤ W := map_subtype_le _
  have hcompl := BinaryAlternatingFiveFixedPoint.isCompl_core_typeSpan_typeReject τ
  have noModel (N : Subgroup G) (hNR : N ≤ R)
      (hmN : IsConjugationModel L N a5Module) : False := by
    obtain ⟨f,hfi,hfN⟩ := a5_model_core_embedding e0 τ hτ (hNR.trans hRW) hmN
    let : Nontrivial (core (Fin 5)) := Module.nontrivial_of_finrank_pos
      (R := ZMod 2) (M := core (Fin 5)) (by rw [finrank_core]; decide)
    obtain ⟨v,hv⟩ := exists_ne (0 : core (Fin 5))
    have hvR : f v ∈ R₀.toSubmodule := by
      obtain ⟨w,hw,he⟩ := hNR (hfN v)
      have he' : w = (f v).toMul := Subtype.ext he
      exact he' ▸ hw
    have hvS : f v ∈ typeSpan τ (alternatingCoreRepresentation (Fin 5)) :=
      (show f.range ≤ typeSpan τ _ from le_iSup _ f) ⟨v,rfl⟩
    have hz : f v = 0 := hcompl.disjoint.le_bot ⟨hvS,hvR⟩
    exact hv (hfi (hz.trans (map_zero f).symm))
  have hRzero : R₀ = ⊥ := by
    by_contra hRne
    have hRne' : R ≠ ⊥ := by
      intro hz
      apply hRne
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro v hv
      have hvR : (v.toMul : G) ∈ R := ⟨v.toMul,hv,rfl⟩
      have hv1 : (v.toMul : G) = 1 := mem_bot.mp (hz ▸ hvR)
      change v = 0
      apply Additive.toMul.injective
      exact Subtype.ext hv1
    have hJR : J ≤ normalizer (R : Set G) := by
      apply le_normalizer_iff.mpr
      intro g hg x hx
      obtain ⟨w,hw,rfl⟩ := hx
      let g₀ : J := ⟨g,hg⟩
      have hv : ρ (q g₀) (Additive.ofMul w) ∈ R₀.toSubmodule :=
        marked_a5_reject_stable ρ K eK (q g₀) (Additive.ofMul w) hw
      exact ⟨(ρ (q g₀) (Additive.ofMul w)).toMul,hv,hρ g₀ (Additive.ofMul w)⟩
    obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hi.outside
    have hfixed : W ⊓ centralizer (L : Set G) = ⊥ :=
      hi.reduced_fixed_eq_bot_of_outside_centralizes hH
        (hi.omega_centralizes_of_thompson_centralizes hH hj)
    have hnon : ⁅R,L⁆ ≠ ⊥ := by
      intro hz
      apply hRne'
      apply bot_unique
      intro r hr
      apply hfixed.le
      exact ⟨hRW hr,(commutator_eq_bot_iff_le_centralizer.mp hz) hr⟩
    have hRInput := hi.invariant_subgroup_input hRW
      (le_sup_left.trans hJR) (le_sup_right.trans hJR) hnon
    obtain ⟨N,D,hNR,horbit,hfixedN,hmodels⟩ := hRInput.stationary_reduced_seed_models
      (hj.trans (centralizer_le hRW))
    have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) := by
      rw [←horbit]
      exact D.sourceOrbit_weakClosure_setup.normalizes
    rcases hmodels with hnat | ⟨s,hns,hs,hmN⟩
    · have hNW : N = W := original_natural_seed_eq_layer h hout (hNR.trans hRW) hnat hTN
      apply noModel U
      · have hWR : W ≤ R := by rw [←hNW]; exact hNR
        exact hUW.trans hWR
      · exact ⟨e0,f0,hf0⟩
    · have hs1 : s = 1 := by omega
      subst s
      let : NeZero 1 := ⟨by decide⟩
      exact noModel N hNR hmN.a5_of_hermitian_one
  obtain ⟨k,c,hc⟩ := BinaryAlternatingFiveFixedPoint.exists_core_coordinates_of_typeReject_eq_bot τ hRzero
  have hsup : B ⊔ (S : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have htwo : IsPGroup 2 (Q ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K ((S : Subgroup J).map q) (S.isPGroup'.map q) (by
      rw [←Subgroup.map_sup,hsup,map_top_of_surjective q hq])
  have hz : center K = ⊥ := by
    apply bot_unique
    intro x hx
    apply eK₀.map_eq_one_iff.mp
    exact hi.quotient_center_eq_bot.le (MulEquivClass.apply_mem_center eK₀ hx)
  have hCK : centralizer (K : Set Q) = ⊥ := by
    have hp := centralizer_isPGroup_of_centerless_quotient K hz htwo
    have hh : centralizer (K : Set Q) ≤ pCore 2 Q := le_sSup ⟨inferInstance,hp⟩
    exact bot_unique (hh.trans_eq (pCore_quotient_pCore_eq_bot (G:=J) 2))
  obtain ⟨p,hp,hcov⟩ := AlternatingFive.exists_symmetric_actor_of_centralizer_eq_bot ρ K eK hCK
  let coords : AlternatingFive.AmplifiedDeleted.Coordinates (ι := Fin k) τ := ⟨c,hc⟩
  have hk2 := AlternatingFive.deleted_multiplicity_le_two_of_faithful_symmetric_action
    ρ τ p hp coords hcov hcubic
  have hk0 : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    subst k
    let : Subsingleton (Additive W) := c.injective.subsingleton
    apply h.nontrivial_action
    apply bot_unique
    intro w hw
    exact congrArg (fun v : Additive W => (v.toMul : G))
      (Subsingleton.elim (Additive.ofMul ⟨w,hw⟩) 0)
  let d := coreEquivNatural (Fin 5) (by decide)
  let cn := c.trans (LinearEquiv.piCongrRight fun _ : Fin k => d)
  have hcn (g : alternatingGroup (Fin 5)) (v : Additive W) :
      cn (τ g v) = a5Copies k g (cn v) := by
    change (fun j => d (c (τ g v) j)) = _
    rw [hc]
    funext j
    exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val (c v j)
  let f : W ≃* Multiplicative (Fin k → natural (Fin 5)) :=
    (MulEquiv.refl W).trans cn.toAddEquiv.toMultiplicative
  have hmodel : IsConjugationModel L W (a5Copies k) := by
    refine ⟨e0,f,?_⟩
    intro l w
    have he := hcn (e0 (QuotientGroup.mk' (pCore 2 L) l)) (Additive.ofMul w)
    change (f.symm (Multiplicative.ofAdd
      (a5Copies k (e0 (QuotientGroup.mk' (pCore 2 L) l)) (cn (Additive.ofMul w)))) : G) = _
    rw [←he]
    change ((cn.symm (cn (τ (e0 (QuotientGroup.mk' (pCore 2 L) l))
      (Additive.ofMul w)))).toMul : G) = _
    rw [cn.symm_apply_apply]
    exact hτ l (Additive.ofMul w)
  exact h.not_a5 (oneOrTwoA5Modules_of_copies hk0 hk2 hmodel)

/-- At field degree two, original stationary seed selection yields a full
natural model on the actual moved layer; the deleted A₅ alternative is excluded. -/
theorem original_stationary_degree_two_natural
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hj : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (layer L V : Set G)) (hn : n = 2) :
    IsNaturalModule L (layer L V) n := by
  obtain ⟨N,D,hNW,horbit,hfixed,hmodels⟩ := h.stationary_layer_seed_models hout hj
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) := by
    rw [←horbit]
    exact D.sourceOrbit_weakClosure_setup.normalizes
  rcases hmodels with hnat | ⟨s,hns,hs,hm⟩
  · exact original_natural_seed_eq_layer h hout hNW hnat hTN ▸ hnat
  · have hs1 : s = 1 := by omega
    subst s
    let : NeZero 1 := ⟨by decide⟩
    exact (original_stationary_a5_seed_false h hout hj hn hNW hm.a5_of_hermitian_one).elim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
