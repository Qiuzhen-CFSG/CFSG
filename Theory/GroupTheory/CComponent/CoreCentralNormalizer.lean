module

public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# A noncentral subgroup detects its component normalizer

Distinct components commute after quotienting by the ambient two-core.
A subgroup of K fixed by a proposed mover then centralizes K/O₂(K), so
its literal action on the core-central quotient is trivial. A nontrivial
such action therefore forces the original normalizer to preserve K.

Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

private theorem image_eq_bot_of_commutator_le (K X : Subgroup G)
    (hcomm : ⁅K,X⁆ ≤ K.pCoreIn 2) : coreCentralActorImage K X = ⊥ := by
  apply eq_bot_iff.mpr
  rintro _ ⟨x,hx,rfl⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)) z
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
  change normalizerCoreCentralAction K x (coreCentralProjection K k) = coreCentralProjection K k
  rw [normalizerCoreCentralAction_apply]
  let y := K.normalizerMonoidHom x k
  have hck : (y * k⁻¹ : K).val ∈ K.pCoreIn 2 := by
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator hx k.property
  obtain ⟨v,hv,he⟩ := hck
  have hvq : coreCentralProjection K v = 1 := by
    change QuotientGroup.mk' (center (K ⧸ pCore 2 K)) (QuotientGroup.mk' (pCore 2 K) v) = 1
    have hv0 : QuotientGroup.mk' (pCore 2 K) v = 1 := (QuotientGroup.eq_one_iff v).mpr hv
    rw [hv0,map_one]
  have hev : v = y*k⁻¹ := Subtype.ext he
  rw [hev,map_mul,map_inv] at hvq
  exact mul_inv_eq_one.mp hvq

variable [Finite G]

private theorem commutator_le_of_normalized_subgroup_of_not_normalizes
    {K : Subgroup G} (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (X : Subgroup G) (hXK : X ≤ K) (g : G) (hg : g ∈ normalizer (X : Set G))
    (hgn : g ∉ normalizer (K : Set G)) : ⁅K,X⁆ ≤ K.pCoreIn 2 := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let e := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hB : IsComponent (G ⧸ pCore 2 G) B := ⟨(hK.map_quotient _).subnormal,inferInstance⟩
  let D := K.map (MulAut.conj g).toMonoidHom
  have hD := hK.map_equiv (MulAut.conj g)
  have hmap : D.map q = B.map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hneq : B ≠ B.map (MulAut.conj (q g)).toMonoidHom := by
    intro he
    apply hgn
    have hh : q g ∈ normalizer (B : Set (G ⧸ pCore 2 G)) :=
      mem_normalizer_iff_map_conj_eq.mpr he.symm
    have hh' : g ∈ (normalizer (K.map q)).comap q := hh
    rwa [normalizer_cComponent_quotient hK (pCore 2 G)] at hh'
  have hc : ⁅B,D.map q⁆ = ⊥ := by
    rw [hmap]
    exact hB.commutator_eq_bot_of_ne (hB.map_conj (q g)) hneq
  have hcore := (cComponent_commutator_le_twoCores_of_quotient_commutes hK hD hc).1.trans inf_le_left
  have hXD : X ≤ D := by
    rw [←mem_normalizer_iff_map_conj_eq.mp hg]
    exact map_mono hXK
  exact (commutator_mono le_rfl hXD).trans hcore

/-- Within the original component overgroup, the normalizer of a subgroup
with nontrivial core-central component action preserves that component. -/
theorem normalizer_inf_le_of_coreCentral_image_ne_bot
    (H K X : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hXK : X ≤ K) (hne : coreCentralActorImage K X ≠ ⊥) :
    H ⊓ normalizer (X : Set G) ≤ normalizer (K : Set G) := by
  let B := K.subgroupOf H
  let Y := X.subgroupOf H
  let e : B ≃* K := subgroupOfEquivOfLe hKH
  let eq := QuotientGroup.congr (pCore 2 B) (pCore 2 K) e (pCore_map_iso 2 e)
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eq.symm
  intro g hg
  by_contra hgn
  let u : H := ⟨g,hg.1⟩
  have huY : u ∈ normalizer (Y : Set H) := by
    rw [←subgroupOf_normalizer_eq (hXK.trans hKH)]
    exact hg.2
  have huB : u ∉ normalizer (B : Set H) := by
    rw [←subgroupOf_normalizer_eq hKH]
    exact hgn
  have hc := commutator_le_of_normalized_subgroup_of_not_normalizes hK Y
    (comap_mono hXK) u huY huB
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hKH,
    map_subgroupOf_eq_of_le (hXK.trans hKH),pCoreIn_subgroupOf 2 K H hKH,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 K).trans hKH)] at hm
  exact hne (image_eq_bot_of_commutator_le K X hm)

end Subgroup
