module
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Conjugation displacement and the ambient commutator

A surjective actor map intertwining an elementary abelian subgroup's
conjugation action identifies the binary displacement span with the literal
ambient commutator. This keeps the relative normalization convention explicit.
Used for the reciprocal module calculation in Aschbacher--Smith 11.3.6,
printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G J : Type*} [Group G] [Group J] {A W : Subgroup G}
  [IsElementaryAbelian 2 W]

/-- The binary displacement span is the literal ambient commutator, whenever
all actors are lifted through the given conjugation action. -/
theorem coinvariants_card_of_conjugation [Finite G]
    (hAW : A ≤ normalizer (W : Set G))
    (ρ : Representation (ZMod 2) J (Additive W))
    (f : A →* J) (hf : Function.Surjective f)
    (he : ∀ a : A, ∀ w : W,
      (ρ (f a) (Additive.ofMul w)).toMul =
        W.normalizerMonoidHom (inclusion hAW a) w) :
    Nat.card (Coinvariants.ker ρ) = Nat.card (⁅A,W⁆ : Subgroup G) := by
  let C := ⁅A,W⁆.subgroupOf W
  let U : Submodule (ZMod 2) (Additive W) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup C)
  have hle : ⁅A,W⁆ ≤ W := le_normalizer_iff_commutator_le_right.mp hAW
  have hU : Coinvariants.ker ρ = U := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,w⟩,rfl⟩
      obtain ⟨a,rfl⟩ := hf g
      simp only [sub_eq_add_neg]
      change ((ρ (f a) w).toMul * w.toMul⁻¹ : W).val ∈ ⁅A,W⁆
      have hew := he a w.toMul
      rw [ofMul_toMul] at hew
      rw [hew]
      exact commutator_mem_commutator a.property w.toMul.property
    · intro w hw
      have hc : C.map W.subtype ≤
          ((Subgroup.toAddSubgroup.symm
            ((AddSubgroup.toZModSubmodule 2).symm (Coinvariants.ker ρ)))).map W.subtype := by
        rw [map_subgroupOf_eq_of_le hle]
        apply commutator_le.mpr
        intro a ha v hv
        let a' : A := ⟨a,ha⟩
        let v' : W := ⟨v,hv⟩
        have hz := Coinvariants.sub_mem_ker (ρ := ρ) (f a') (Additive.ofMul v')
        refine ⟨W.normalizerMonoidHom (inclusion hAW a') v' * v'⁻¹,?_,rfl⟩
        change Additive.ofMul (W.normalizerMonoidHom (inclusion hAW a') v' * v'⁻¹) ∈ Coinvariants.ker ρ
        rw [← he a' v']
        simpa only [ofMul_mul,ofMul_inv,ofMul_toMul,sub_eq_add_neg] using hz
      have hh := hc (show (w.toMul : G) ∈ C.map W.subtype from ⟨w.toMul,hw,rfl⟩)
      obtain ⟨v,hv,hv'⟩ := hh
      have hvw : v = w.toMul := Subtype.ext hv'
      change Additive.ofMul v ∈ Coinvariants.ker ρ at hv
      rwa [hvw] at hv
  rw [hU]
  let e : U ≃ C :=
    { toFun := fun w => ⟨w.val.toMul,w.property⟩
      invFun := fun w => ⟨Additive.ofMul w.val,w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
