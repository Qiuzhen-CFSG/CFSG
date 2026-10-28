module
public import Theory.Representation.SymplecticFourOrthogonalCover.HyperplaneMovement

/-!
# Nontrivial field-subspace movement in a full central cover

A nonzero displacement on the preimage of a field subspace has at least
q distinct commutator values: lift the scalar multiples of a moved vector
through the original projection. Fixed-vector lifting ensures a nontrivial
commutator has nonzero natural displacement, even with the full central
attachment. The fixed-space application uses the literal embedded centralizer.

The critical-root application is NonbinarySymplectic.CriticalReduction.EqualRootJoined.
Source: MS93 (3.3)(ii) and (5.7), printed pp.867,919.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace Representation.SymplecticFourOrthogonalCover

variable {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
  {σ : Representation (ZMod 2) (L (K := F)) W}

/-- A nontrivial action on a full field-subspace preimage has at least a
field's worth of commutators, retaining all central attachments. -/
theorem embedded_subspace_commutator_card_ge_field
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y A : Subgroup G) (D : Submodule F (Vector F)) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hA : ∀ w : W, j (Multiplicative.ofAdd w) ∈ A ↔ p w ∈ D)
    (hAr : A ≤ j.range) (hn : ⁅Y,A⁆ ≠ ⊥) :
    Nat.card F ≤ Nat.card (⁅Y,A⁆ : Subgroup G) := by
  classical
  have hdisp (y : Y) (w : W) :
      j (Multiplicative.ofAdd (σ (β y) w-w))=⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  have hex : ∃ y ∈ Y, ∃ a ∈ A, ⁅y,a⁆ ≠ 1 := by
    by_contra! hh
    apply hn
    apply le_bot_iff.mp
    exact commutator_le.mpr fun y hy a ha => mem_bot.mpr (hh y hy a ha)
  obtain ⟨y,hy,a,ha,hne⟩ := hex
  obtain ⟨w,rfl⟩ := hAr ha
  let δ := symplecticNatural (k := F) 2 (β ⟨y,hy⟩).val (p w.toAdd)-p w.toAdd
  have hd : δ ≠ 0 := by
    intro hd
    have hf := cover_fixed_of_projection_fixed p hp (β ⟨y,hy⟩) w.toAdd
      (sub_eq_zero.mp hd)
    apply hne
    change ⁅(⟨y,hy⟩ : Y).val,j (Multiplicative.ofAdd w.toAdd)⁆=1
    rw [←hdisp,hf,sub_self,ofAdd_zero,map_one]
  have hchoose (t : F) : ∃ u : W, p u=t • p w.toAdd := hp.1 _
  choose u hu using hchoose
  have hmem (t : F) : j (Multiplicative.ofAdd (u t)) ∈ A :=
    (hA _).mpr (hu t ▸ D.smul_mem t ((hA _).mp ha))
  let f : F → (⁅Y,A⁆ : Subgroup G) := fun t =>
    ⟨⁅y,j (Multiplicative.ofAdd (u t))⁆,commutator_mem_commutator hy (hmem t)⟩
  have hf : Function.Injective f := by
    intro t s he
    have he' : j (Multiplicative.ofAdd (σ (β ⟨y,hy⟩) (u t)-u t))=
        j (Multiplicative.ofAdd (σ (β ⟨y,hy⟩) (u s)-u s)) := by
      rw [hdisp,hdisp]
      exact congrArg Subtype.val he
    have hv := congrArg p (Multiplicative.ofAdd.injective (hj he'))
    rw [map_sub,map_sub,p.isIntertwining,p.isIntertwining,hu t,hu s] at hv
    change symplecticNatural 2 (β ⟨y,hy⟩).val (t • p w.toAdd)-t • p w.toAdd =
      symplecticNatural 2 (β ⟨y,hy⟩).val (s • p w.toAdd)-s • p w.toAdd at hv
    rw [map_smul,map_smul,←smul_sub,←smul_sub] at hv
    exact (smul_left_injective F hd) hv
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite j.range := Finite.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hbound : ⁅Y,A⁆ ≤ j.range := by
    apply commutator_le.mpr
    intro y hy a ha
    obtain ⟨w,rfl⟩ := hAr ha
    change ⁅(⟨y,hy⟩ : Y).val,j (Multiplicative.ofAdd w.toAdd)⁆ ∈ j.range
    rw [←hdisp]
    exact ⟨_,rfl⟩
  let : Finite (⁅Y,A⁆ : Subgroup G) :=
    Finite.of_injective (inclusion hbound) (inclusion_injective _)
  exact Nat.card_le_card_of_injective f hf

/-- The full centralizer of an embedded actor is a field-subspace preimage,
so every nontrivial commutator with it has at least field order. -/
theorem embedded_fixed_subspace_commutator_card_ge_field
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T : Subgroup G) (β : Y →* L (K := F)) (γ : T →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hactT : ∀ (t : T) (w : W), j (Multiplicative.ofAdd (σ (γ t) w)) =
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (hn : ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ ≠ ⊥) :
    Nat.card F ≤ Nat.card (⁅Y,j.range ⊓ centralizer (T : Set G)⁆ : Subgroup G) := by
  let α := (commutator (Sp F)).subtype.comp γ
  apply embedded_subspace_commutator_card_ge_field p hp j hj Y
    (j.range ⊓ centralizer (T : Set G)) (TwoLocalCover.fixedSpace α.range) β hact
    ?_ inf_le_left hn
  intro w
  constructor
  · intro hw t ht
    obtain ⟨t,rfl⟩ := ht
    have he : σ (γ t) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hactT,hw.2 t.val t.property,mul_inv_cancel_right]
    exact (LinearMap.congr_fun (p.isIntertwining' (γ t)) w).symm.trans (congrArg p he)
  · intro hw
    refine ⟨⟨_,rfl⟩,fun t ht => ?_⟩
    have hf := cover_fixed_of_projection_fixed p hp (γ ⟨t,ht⟩) w
      (hw (α ⟨t,ht⟩) ⟨_,rfl⟩)
    have he := congrArg (fun w => j (Multiplicative.ofAdd w)) hf
    rw [hactT,mul_inv_eq_iff_eq_mul] at he
    exact he

end Representation.SymplecticFourOrthogonalCover
