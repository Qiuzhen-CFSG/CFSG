module

public import Theory.GroupTheory.CoreCentralNormalizerAction.QuinticInnerSubgroup

/-!
# Lifting a quintic inverter through the entire original action

An inverter in the literal projected component Sylow lifts to that supplied
Sylow. Equal indices five identify the inverse image of the inner subgroup's
two-core with the whole original residual's two-core. The central kernel is
retained and no order-two lift is assumed.

Source application: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem core_preimage_of_equal_index {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (f : A →* B) (hf : Function.Surjective f)
    (hA : Nat.card (A ⧸ pCore 2 A) = 5)
    (hB : Nat.card (B ⧸ pCore 2 B) = 5) :
    (pCore 2 B).comap f = pCore 2 A := by
  have hle : pCore 2 A ≤ (pCore 2 B).comap f := map_le_iff_le_comap.mp
    (le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩)
  have hi : ((pCore 2 B).comap f).index = 5 := by
    rw [index_comap_of_surjective _ hf]
    exact hB
  have hj : (pCore 2 A).index = 5 := hA
  have hk := ((pCore 2 B).comap f).card_mul_index
  have hc := (pCore 2 A).card_mul_index
  rw [hi] at hk
  rw [hj] at hc
  exact (eq_of_le_of_card_ge hle (by omega)).symm

/-- An inverter of the literal inner quotient lifts into the original
component Sylow and inverts the original residual modulo its full two-core. -/
theorem coreCentral_quintic_sylow_inverter_lift
    (K X : Subgroup G) (U : Sylow 2 K)
    (hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G))
    (hXN : X ≤ normalizer (K : Set G))
    (hz : center (coreCentralQuotient K) = ⊥)
    (hinner : coreCentralActorImage K X ≤ MulAut.innerSubgroup (coreCentralQuotient K))
    (hXfive : Nat.card (X ⧸ pCore 2 X) = 5) :
    let C := coreCentralQuotient K
    let Y := (coreCentralActorImage K X).comap (MulAut.conj : C →* MulAut C)
    Nat.card (Y ⧸ pCore 2 Y) = 5 →
    (∃ u ∈ (U : Subgroup K).map (coreCentralProjection K),
      ∀ y ∈ Y, u*y*u⁻¹*y ∈ Y.pCoreIn 2) →
    ∃ k : K, k ∈ U ∧ ∀ x ∈ X, (k:G)*x*(k:G)⁻¹*x ∈ X.pCoreIn 2 := by
  let C := coreCentralQuotient K
  let q := coreCentralProjection K
  let a := normalizerCoreCentralAction K
  let B := coreCentralActorImage K X
  let c : C →* MulAut C := MulAut.conj
  let Y := B.comap c
  dsimp only
  intro hYfive hinv
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have ha (k : K) : a ⟨k,K.le_normalizer k.property⟩ = c (q k) := by
    ext y
    obtain ⟨x,rfl⟩ := hq y
    rw [normalizerCoreCentralAction_apply,MulAut.conj_apply,←map_inv,←map_mul,←map_mul]
    rfl
  have hc : Function.Injective c := conj_injective_of_center_eq_bot hz
  have hYB : Y.map c = B := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hinner
  let e : Y ≃* B := (Y.equivMapOfInjective c hc).trans (MulEquiv.subgroupCongr hYB)
  let ex := (subgroupOfEquivOfLe hXN).symm
  let f : X →* B := (a.subgroupMap (X.subgroupOf (normalizer (K : Set G)))).comp ex.toMonoidHom
  have hf : Function.Surjective f := (a.subgroupMap_surjective _).comp ex.surjective
  let g : X →* Y := e.symm.toMonoidHom.comp f
  have hg : Function.Surjective g := e.symm.surjective.comp hf
  have hcg (x : X) : c (g x : C) = a ⟨x,hXN x.property⟩ := by
    exact congrArg Subtype.val (e.apply_symm_apply (f x))
  have hcore := core_preimage_of_equal_index g hg hXfive hYfive
  obtain ⟨u,⟨k,hk,rfl⟩,hinv⟩ := hinv
  refine ⟨k,hk,?_⟩
  intro x hx
  have hkX : (k:G) ∈ normalizer (X : Set G) := hUX (mem_map_of_mem K.subtype hk)
  let z : X := ⟨(k:G)*x*(k:G)⁻¹*x,
    X.mul_mem ((mem_normalizer_iff.mp hkX x).mp hx) hx⟩
  let v : X := ⟨x,hx⟩
  have he : (g z : C) = q k * (g v:C) * (q k)⁻¹ * (g v:C) := by
    apply hc
    rw [map_mul,map_mul,map_mul,map_inv,hcg,hcg,←ha]
    change a (⟨k,K.le_normalizer k.property⟩ * ⟨x,hXN hx⟩ *
      ⟨k,K.le_normalizer k.property⟩⁻¹ * ⟨x,hXN hx⟩) = _
    simp only [map_mul,map_inv]
    rfl
  have hzcore : g z ∈ pCore 2 Y := by
    have hh := hinv (g v) (g v).property
    rw [←he] at hh
    exact (mem_map_iff_mem Y.subtype_injective).mp hh
  have hzX : z ∈ pCore 2 X := by
    rw [←hcore]
    exact hzcore
  exact mem_map_of_mem X.subtype hzX

end Theory.GroupTheory
