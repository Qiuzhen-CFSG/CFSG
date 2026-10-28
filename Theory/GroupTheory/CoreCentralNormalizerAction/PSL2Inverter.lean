module

public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.SpecificGroups.PSL2.QuinticSylowInverter

/-!
# An inverter in the original component Sylow subgroup

Pull the five-subgroup back through the faithful inner action on the literal
core-central quotient. The supplied component Sylow maps onto a Sylow of that
quotient. The PSL₂ inverter therefore lifts into that original component Sylow;
only its quotient image is asserted to be an involution.

Source application: Aschbacher--Smith 6.1.4, printed p.666.
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

/-- An actual component Sylow contains a lift of an inverter of the whole
five-element inner action image. All quotient maps are the original maps. -/
theorem coreCentral_odd_quintic_sylow_inverter
    (K X : Subgroup G) (U : Sylow 2 K)
    (hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G))
    (hinner : coreCentralActorImage K X ≤ MulAut.innerSubgroup (coreCentralQuotient K))
    (hfive : Nat.card (coreCentralActorImage K X) = 5)
    {F : Type*} [Field F] [Finite F] (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (e : coreCentralQuotient K ≃* PSL(2,F)) :
    ∃ k : K, k ∈ U ∧ IsInvolution (coreCentralProjection K k) ∧
      ∀ x : normalizer (K : Set G), (x : G) ∈ X →
        normalizerCoreCentralAction K ⟨k,K.le_normalizer k.property⟩ *
          normalizerCoreCentralAction K x *
          (normalizerCoreCentralAction K ⟨k,K.le_normalizer k.property⟩)⁻¹ =
        (normalizerCoreCentralAction K x)⁻¹ := by
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
  obtain ⟨t,ht,hti,htR⟩ := Theory.PSL2.odd_quintic_sylow_inverter hF Rm hRm Sm hSm
  obtain ⟨s,hs,rfl⟩ := ht
  obtain ⟨k,hk,rfl⟩ := hs
  change IsInvolution (e (q k)) at hti
  change ∀ x ∈ Rm, e (q k) * x * (e (q k))⁻¹ = x⁻¹ at htR
  refine ⟨k,hk,?_,?_⟩
  · constructor
    · intro he
      exact hti.1 (by simp only [q,he,map_one])
    · apply e.injective
      simpa only [q,map_pow,map_one] using hti.2
  · intro x hx
    have hy : a x ∈ Y := mem_map_of_mem a hx
    have hyr : a x ∈ R.map c := hRY ▸ hy
    obtain ⟨y,hy,hyx⟩ := hyr
    have hi := htR (e y) (mem_map_of_mem e.toMonoidHom hy)
    have hi' : q k * y * (q k)⁻¹ = y⁻¹ := by
      apply e.injective
      simpa only [map_mul,map_inv] using hi
    change a _ * a x * (a _)⁻¹ = (a x)⁻¹
    rw [←hyx,action_inner]
    exact (by simpa only [map_mul,map_inv] using congrArg c hi')

end Theory.GroupTheory
