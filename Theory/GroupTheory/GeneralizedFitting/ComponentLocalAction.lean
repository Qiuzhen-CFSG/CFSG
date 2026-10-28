module
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitAutomizer
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.NormalizerAction.Simple
/-!
# The component core action and the faithful normalizer quotient

The local product K N_T(K) surjects onto N_G(K)/C_G(K) when the Sylow
orbit of K is the two-residual. For a two-core-free K, transport by its
quotient map identifies that literal quotient with the range of the
core-quotient action. The same equivalence retains stabilizer, actor and
maximal-subgroup images; no choice of a different actor is involved.
Source: Aschbacher–Smith E.1.11 and E.2.2, pp.213–216.
-/
@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

def componentLocalQuotient (T : Subgroup G) (K : Subgroup G) :
    (K ⊔ (T ⊓ normalizer (K : Set G)) : Subgroup G) →* NormalizerAction.Star K :=
  (NormalizerAction.quotient K).comp (inclusion (sup_le K.le_normalizer inf_le_right))

variable [Finite G]
theorem componentLocalQuotient_surjective (T : Sylow 2 G) {K : Subgroup G}
    (hK : IsComponent G K) (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G) :
    Function.Surjective (componentLocalQuotient (T : Subgroup G) K) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← component_automizer_sylow_supplement T hK ho]
  apply sup_le
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x,mem_sup_left hx⟩,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x,mem_sup_right ⟨hx,x.property⟩⟩,rfl⟩

omit [Finite G] in
theorem quotientAut_injective_of_pCore_eq_bot (K : Subgroup G) (hcore : pCore 2 K=⊥) :
    Function.Injective (quotientAut (pCore 2 K)) := by
  intro a b h
  apply MulEquiv.ext
  intro x
  apply (MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' (pCore 2 K))).mp
    ((QuotientGroup.ker_mk' _).trans hcore)
  have hx := DFunLike.congr_fun h (QuotientGroup.mk' (pCore 2 K) x)
  simpa only [quotientAut_apply_mk] using hx

noncomputable def componentCoreActionEquiv (T : Sylow 2 G) {K : Subgroup G}
    (hK : IsComponent G K) (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G)
    (hcore : pCore 2 K=⊥) :
    NormalizerAction.Star K ≃*
      (pCoreJoinAction 2 (show (T : Subgroup G) ⊓ normalizer K ≤ normalizer K from inf_le_right)).range := by
  let ψ := (quotientAut (pCore 2 K)).comp (NormalizerAction.action K)
  have hi : Function.Injective ψ :=
    (quotientAut_injective_of_pCore_eq_bot K hcore).comp (NormalizerAction.action_injective K)
  have hs := componentLocalQuotient_surjective T hK ho
  have he : ψ.range =
      (pCoreJoinAction 2 (show (T : Subgroup G) ⊓ normalizer K ≤ normalizer K from inf_le_right)).range := by
    change ψ.range = (ψ.comp (componentLocalQuotient (T : Subgroup G) K)).range
    conv_rhs => rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hs,←MonoidHom.range_eq_map]
  exact (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr he)

theorem componentCoreActionEquiv_local (T : Sylow 2 G) {K : Subgroup G}
    (hK : IsComponent G K) (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G)
    (hcore : pCore 2 K=⊥) (x : (K ⊔ ((T : Subgroup G) ⊓ normalizer K) : Subgroup G)) :
    componentCoreActionEquiv T hK ho hcore (componentLocalQuotient (T : Subgroup G) K x) =
      (pCoreJoinAction 2 (show (T : Subgroup G) ⊓ normalizer K ≤ normalizer K from inf_le_right)).rangeRestrict x := by
  apply Subtype.ext
  rfl
omit [Finite G] in
theorem componentLocalQuotient_stabilizer_image (T : Subgroup G) (K : Subgroup G) :
    (T.subgroupOf (normalizer (K : Set G))).map (NormalizerAction.quotient K) =
      ((T ⊓ normalizer K).subgroupOf (K ⊔ (T ⊓ normalizer K))).map
        (componentLocalQuotient T K) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,mem_sup_right ⟨hx,x.property⟩⟩,⟨hx,x.property⟩,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,(sup_le K.le_normalizer inf_le_right) x.property⟩,hx.1,rfl⟩

omit [Finite G] in
theorem componentLocalQuotient_overgroup_image_le (T K M : Subgroup G) :
    (M.subgroupOf (K ⊔ (T ⊓ normalizer K))).map (componentLocalQuotient T K) ≤
      (M.subgroupOf (normalizer (K : Set G))).map (NormalizerAction.quotient K) := by
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨⟨x,(sup_le K.le_normalizer inf_le_right) x.property⟩,hx,rfl⟩

theorem componentCoreActionEquiv_map (T : Sylow 2 G) {K : Subgroup G}
    (hK : IsComponent G K) (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G)
    (hcore : pCore 2 K=⊥)
    (A : Subgroup (K ⊔ ((T : Subgroup G) ⊓ normalizer K) : Subgroup G)) :
    (A.map (componentLocalQuotient (T : Subgroup G) K)).map
        (componentCoreActionEquiv T hK ho hcore).toMonoidHom =
      A.map (pCoreJoinAction 2 (show (T : Subgroup G) ⊓ normalizer K ≤ normalizer K from inf_le_right)).rangeRestrict := by
  rw [map_map]
  rfl
end Theory.GroupTheory
