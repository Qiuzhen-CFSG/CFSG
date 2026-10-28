module

public import Theory.GroupTheory.CoreCentralNormalizerAction.PSL2Inverter
public import Theory.SpecificGroups.PSL2.QuinticNineExclusion

/-!
# Field bounds from the original component Sylow marking

The actual component Sylow maps onto a Sylow in the literal central
quotient. Its normalized order-five inner image forces the odd field
size to exceed three and to differ from nine. In particular the exceptional
nine-field central cover is excluded before any cover kernel is discarded.

Source: Aschbacher--Smith A.3.15(1) and 6.1.4, pp.50--51 and666.
-/

public noncomputable section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem projection_surjective (K : Subgroup G) :
    Function.Surjective (coreCentralProjection K) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

private theorem action_inner (K : Subgroup G) (k : K) :
    normalizerCoreCentralAction K ⟨k,K.le_normalizer k.property⟩ =
      MulAut.conj (coreCentralProjection K k) := by
  ext y
  obtain ⟨x,rfl⟩ := projection_surjective K y
  rw [normalizerCoreCentralAction_apply,MulAut.conj_apply,←map_inv,←map_mul,←map_mul]
  rfl

variable [Finite G]

/-- The original component-Sylow action supplies the field bounds needed
for the faithful nonexceptional PSL₂ cover. -/
theorem coreCentral_odd_quintic_field_bounds
    (K X : Subgroup G) (U : Sylow 2 K)
    (hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G))
    (hinner : coreCentralActorImage K X ≤ MulAut.innerSubgroup (coreCentralQuotient K))
    (hfive : Nat.card (coreCentralActorImage K X) = 5)
    {F : Type*} [Field F] [Finite F] (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (e : coreCentralQuotient K ≃* PSL(2,F)) :
    3 < Nat.card F ∧ Nat.card F ≠ 9 := by
  let C := coreCentralQuotient K
  let q := coreCentralProjection K
  let a := normalizerCoreCentralAction K
  let Y := coreCentralActorImage K X
  let c : C →* MulAut C := MulAut.conj
  have hz : center C = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center PSL(2,F) at he
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  have hc : Function.Injective c := conj_injective_of_center_eq_bot hz
  let R := Y.comap c
  have hRY : R.map c = Y := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hinner
  have hRfive : Nat.card R = 5 := by
    rw [←card_map_of_injective hc,hRY]
    exact hfive
  let S := U.mapSurjective (f := q) (projection_surjective K)
  have hSR : (S : Subgroup C) ≤ normalizer (R : Set C) := by
    rintro z ⟨u,hu,rfl⟩
    apply R.mem_normalizer_iff.mpr
    intro y
    change c y ∈ Y ↔ c (q u * y * (q u)⁻¹) ∈ Y
    rw [map_mul,map_mul,map_inv]
    have hn : a ⟨u,K.le_normalizer u.property⟩ ∈ normalizer (Y : Set (MulAut C)) := by
      apply (X.subgroupOf (normalizer (K : Set G))).le_normalizer_map a
      apply mem_map_of_mem
      apply mem_normalizer_iff.mpr
      intro x
      exact mem_normalizer_iff.mp (hUX (mem_map_of_mem K.subtype hu)) (x : G)
    rw [action_inner] at hn
    exact mem_normalizer_iff.mp hn (c y)
  let Sm := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let Rm := R.map e.toMonoidHom
  have hSm : (Sm : Subgroup PSL(2,F)) ≤ normalizer (Rm : Set PSL(2,F)) :=
    (map_mono hSR).trans (R.le_normalizer_map e.toMonoidHom)
  have hRm : Nat.card Rm = 5 := (card_map_of_injective e.injective).trans hRfive
  exact Theory.PSL2.odd_quintic_field_bounds hF Rm hRm Sm hSm

end Theory.GroupTheory
