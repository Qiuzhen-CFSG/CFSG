module
public import Theory.Representation.BinaryConjugationCoordinates.FixedIndex
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Reciprocal conjugate actions without strong offenders

For a faithful binary model without strong offenders, the actor-side
centralizer index is at most the module-side index. Reciprocal conjugate
actions give both inequalities, hence equality. A noncentral actor with
equal indices is an offender in the prescribed model.

This supplies the index and offender inputs in the original binary G₂
commutator argument, Aschbacher--Smith 12.4.9, printed p.816.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace BinaryConjugationCoordinates
variable {G Q M : Type*} [Group G] [Finite G] [Group Q]
  [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

omit [Finite G] [FiniteDimensional (ZMod 2) M] in
private theorem model_range_ne_bot
    (A U : Subgroup G) (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) Q M) (hσ : Function.Injective σ)
    (φ : A →* Q) (e : U ≃* Multiplicative M)
    (he : ∀ (a : A) (u : U),
      (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩ u)).toAdd =
        σ (φ a) (e u).toAdd)
    (hm : ¬ A ≤ centralizer (U : Set G)) : φ.range ≠ ⊥ := by
  intro hb
  apply hm
  intro a ha
  have ha1 : φ ⟨a,ha⟩ = 1 := by
    have hh : φ ⟨a,ha⟩ ∈ φ.range := ⟨⟨a,ha⟩,rfl⟩
    rwa [hb,mem_bot] at hh
  exact (model_kernel A U hAU σ hσ φ e he).le ha1

private theorem elementary_range_card
    (A : Subgroup G) [IsElementaryAbelian 2 A] (φ : A →* Q) :
    Nat.card φ.range = 2 ^ rank φ.range := by
  let : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 φ.range).exists_card_eq
  rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]

/-- Without strong offenders, a noncentral elementary actor has no larger
centralizer index than the module it moves. -/
theorem centralizer_index_le_of_nonStrong
    (A U : Subgroup G) [IsElementaryAbelian 2 A]
    (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) Q M) (hσ : Function.Injective σ)
    (φ : A →* Q) (e : U ≃* Multiplicative M)
    (he : ∀ (a : A) (u : U),
      (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩ u)).toAdd =
        σ (φ a) (e u).toAdd)
    (hn : ¬ IsStrongFFModule σ) (hm : ¬ A ≤ centralizer (U : Set G)) :
    (centralizer (U : Set G)).relIndex A ≤ (centralizer (A : Set G)).relIndex U := by
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hne := model_range_ne_bot A U hAU σ hσ φ e he hm
  have hi : rank φ.range ≤ fixedCodim σ φ.range :=
    Nat.le_of_not_gt (fun hc => hn ⟨φ.range,⟨hne,inferInstance⟩,hc⟩)
  have ha := model_card_range A U hAU σ hσ φ e he
  rw [inf_relIndex_left] at ha
  rw [←ha,elementary_range_card A φ,model_fixed_index A U hAU σ φ e he]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr hi

/-- Equal centralizer indices make the nontrivial elementary model image
an offender. This statement does not require the non-strong hypothesis. -/
theorem model_offender_of_equal_indices
    (A U : Subgroup G) [IsElementaryAbelian 2 A]
    (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) Q M) (hσ : Function.Injective σ)
    (φ : A →* Q) (e : U ≃* Multiplicative M)
    (he : ∀ (a : A) (u : U),
      (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩ u)).toAdd =
        σ (φ a) (e u).toAdd)
    (hm : ¬ A ≤ centralizer (U : Set G))
    (hi : (centralizer (A : Set G)).relIndex U =
      (centralizer (U : Set G)).relIndex A) :
    IsOffender σ φ.range := by
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  refine ⟨⟨model_range_ne_bot A U hAU σ hσ φ e he hm,inferInstance⟩,?_⟩
  have ha := model_card_range A U hAU σ hσ φ e he
  rw [inf_relIndex_left] at ha
  rw [model_fixed_index A U hAU σ φ e he,←ha,elementary_range_card A φ] at hi
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hi.le

omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

/-- Reciprocal noncentral conjugate actions in a model without strong
offenders have equal indices, and the actual image is an offender. -/
theorem reciprocal_conjugate_offender_of_nonStrong
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) Q M) (hσ : Function.Injective σ)
    (φ : H →* Q) (e : U ≃* Multiplicative M)
    (he : ∀ (a : H) (u : U),
      (e (U.normalizerMonoidHom ⟨a.val,hHU a.property⟩ u)).toAdd =
        σ (φ a) (e u).toAdd)
    (hn : ¬ IsStrongFFModule σ) (g : G)
    (h₁ : U.conjBy g ≤ H) (h₂ : U ≤ H.conjBy g)
    (hm : ⁅U,U.conjBy g⁆ ≠ ⊥) :
    (centralizer (U.conjBy g : Set G)).relIndex U =
        (centralizer (U : Set G)).relIndex (U.conjBy g) ∧
      IsOffender σ (φ.comp (inclusion h₁)).range := by
  have hmove : ¬ U.conjBy g ≤ centralizer (U : Set G) := by
    intro hc
    exact hm (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  have hmove' : ¬ U.conjBy g⁻¹ ≤ centralizer (U : Set G) := by
    intro hc
    have hc' := map_mono (f := (MulAut.conj g).toMonoidHom) hc
    rw [centralizer_map_equiv] at hc'
    change (U.conjBy g⁻¹).conjBy g ≤ centralizer (U.conjBy g : Set G) at hc'
    rw [conjBy_inv'] at hc'
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr hc')
  have h₂' : U.conjBy g⁻¹ ≤ H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h₂
    change U.conjBy g⁻¹ ≤ (H.conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  have step (k : G) (hk : U.conjBy k ≤ H)
      (hm : ¬ U.conjBy k ≤ centralizer (U : Set G)) :
      (centralizer (U : Set G)).relIndex (U.conjBy k) ≤
        (centralizer (U.conjBy k : Set G)).relIndex U := by
    let : IsElementaryAbelian 2 (U.conjBy k) := IsElementaryAbelian.map _
    exact centralizer_index_le_of_nonStrong (U.conjBy k) U (hk.trans hHU) σ hσ
      (φ.comp (inclusion hk)) e (fun a u => he (inclusion hk a) u) hn hm
  have hi := step g h₁ hmove
  have hj := step g⁻¹ h₂' hmove'
  have transport (A B : Subgroup G) :
      (centralizer (A.conjBy g : Set G)).relIndex (B.conjBy g) =
        (centralizer (A : Set G)).relIndex B := by
    change (centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      (B.map (MulAut.conj g).toMonoidHom) = _
    rw [←centralizer_map_equiv A (MulAut.conj g)]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have hx := transport U (U.conjBy g⁻¹)
  have hy := transport (U.conjBy g⁻¹) U
  rw [conjBy_inv'] at hx hy
  have hindex : (centralizer (U.conjBy g : Set G)).relIndex U =
      (centralizer (U : Set G)).relIndex (U.conjBy g) := by omega
  refine ⟨hindex,?_⟩
  let : IsElementaryAbelian 2 (U.conjBy g) := IsElementaryAbelian.map _
  exact model_offender_of_equal_indices (U.conjBy g) U (h₁.trans hHU) σ hσ
    (φ.comp (inclusion h₁)) e (fun a u => he (inclusion h₁ a) u) hmove hindex

end BinaryConjugationCoordinates
