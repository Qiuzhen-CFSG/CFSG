module
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.FixedElementaryTransport
public import Mathlib.GroupTheory.IsPerfect
/-!
# Literal normalizer actions on a two-core central quotient

Normalizer conjugation acts on K/O₂(K) and its central quotient. The actual
image of an actor normalizing R stabilizes the image of R∩K. These images
retain perfectness and the two-group property, respectively. Model transport
preserves the displayed stabilizer, so no arbitrary isomorphic two-subgroup
is substituted in the parabolic argument.

Source: Aschbacher--Smith C.4.5--7, printed pp.152--153.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

abbrev coreCentralQuotient (K : Subgroup G) :=
  (K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)

@[expose] def coreCentralProjection (K : Subgroup G) : K →* coreCentralQuotient K :=
  (QuotientGroup.mk' (center (K ⧸ pCore 2 K))).comp (QuotientGroup.mk' (pCore 2 K))


@[expose] noncomputable def coreCentralQuotientCongr {G' : Type*} [Group G']
    {K : Subgroup G} {K' : Subgroup G'} (e : K ≃* K') : coreCentralQuotient K ≃* coreCentralQuotient K' := by
  let q := QuotientGroup.congr (pCore 2 K) (pCore 2 K') e (pCore_map_iso 2 e)
  exact QuotientGroup.congr _ _ q (Theory.GroupTheory.FixedElementary.map_center q)

theorem coreCentralQuotientCongr_apply {G' : Type*} [Group G']
    {K : Subgroup G} {K' : Subgroup G'} (e : K ≃* K') (k : K) :
    coreCentralQuotientCongr e (coreCentralProjection K k) =
      coreCentralProjection K' (e k) := rfl


@[expose] def normalizerCoreCentralAction (K : Subgroup G) :
    normalizer (K : Set G) →* MulAut (coreCentralQuotient K) :=
  (quotientAut (center (K ⧸ pCore 2 K))).comp
    ((quotientAut (pCore 2 K)).comp K.normalizerMonoidHom)

@[expose] def coreCentralActorImage (K A : Subgroup G) :
    Subgroup (MulAut (coreCentralQuotient K)) :=
  (A.subgroupOf (normalizer (K : Set G))).map (normalizerCoreCentralAction K)

@[expose] def coreCentralIntersectionImage (K R : Subgroup G) :
    Subgroup (coreCentralQuotient K) :=
  (R.subgroupOf K).map (coreCentralProjection K)

theorem normalizerCoreCentralAction_apply (K : Subgroup G)
    (a : normalizer (K : Set G)) (k : K) :
    normalizerCoreCentralAction K a (coreCentralProjection K k) =
      coreCentralProjection K (K.normalizerMonoidHom a k) := by
  simp only [normalizerCoreCentralAction,coreCentralProjection,MonoidHom.comp_apply,
    quotientAut_apply_mk]

theorem coreCentralActorImage_perfect (K A : Subgroup G) [Group.IsPerfect A]
    (hAK : A ≤ normalizer (K : Set G)) : Group.IsPerfect (coreCentralActorImage K A) := by
  let e := subgroupOfEquivOfLe hAK
  let : Group.IsPerfect (A.subgroupOf (normalizer (K : Set G))) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.map _

theorem coreCentralIntersectionImage_isPGroup (K R : Subgroup G) (hr : IsPGroup 2 R) :
    IsPGroup 2 (coreCentralIntersectionImage K R) :=
  (hr.comap_of_injective K.subtype K.subtype_injective).map _

variable [Finite G]
theorem coreCentralActorImage_stabilizes (K A R : Subgroup G)
    (hAR : A ≤ normalizer (R : Set G)) :
    coreCentralActorImage K A ≤
      MulAction.stabilizer (MulAut (coreCentralQuotient K)) (coreCentralIntersectionImage K R) := by
  rintro _ ⟨a,ha,rfl⟩
  change (coreCentralIntersectionImage K R).map
    (normalizerCoreCentralAction K a).toMonoidHom = coreCentralIntersectionImage K R
  apply Subgroup.eq_of_le_of_card_ge
  · rintro z ⟨q,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨K.normalizerMonoidHom a k,?_,(normalizerCoreCentralAction_apply K a k).symm⟩
    exact (mem_normalizer_iff.mp (hAR ha) (k : G)).mp hk
  · exact le_of_eq (Subgroup.card_map_of_injective
      (normalizerCoreCentralAction K a).injective).symm

theorem coreCentralActorImage_map_stabilizes {D : Type*} [Group D]
    (K A R : Subgroup G) (hAR : A ≤ normalizer (R : Set G))
    (e : coreCentralQuotient K ≃* D) :
    (coreCentralActorImage K A).map (MulAut.congr e).toMonoidHom ≤
      MulAction.stabilizer (MulAut D) ((coreCentralIntersectionImage K R).map e.toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩
  have hfix := coreCentralActorImage_stabilizes K A R hAR ha
  change (coreCentralIntersectionImage K R).map a.toMonoidHom = _ at hfix
  change ((coreCentralIntersectionImage K R).map e.toMonoidHom).map
    ((MulAut.congr e) a).toMonoidHom = _
  rw [map_map]
  have he : ((MulAut.congr e) a).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp a.toMonoidHom := by
    ext x
    simp
  rw [he,←map_map,hfix]
end Subgroup
