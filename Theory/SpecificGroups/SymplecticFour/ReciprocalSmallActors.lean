module
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.TypeTags.Hom
/-!
# Reciprocal natural actions over the field of four elements

A surjective equivariant quotient of a finite subgroup bounds the index of
its actual centralizer from below by the natural fixed-space quotient.
For two reciprocal symplectic actions these bounds, together with the
upper bound q^(d²) for an actor with d-dimensional displacement, force
both image orders to be four when one is less than sixteen.

This is the small-actor comparison in MS93 (3.3), printed p.867. It assumes
literal inner natural actions; eliminating ambient field twists is separate.
-/

public section
noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
theorem fixed_quotient_card (A : Subgroup (Sp F)) :
    Nat.card (Vector F ⧸ fixedSpace A) = Nat.card F ^ Module.finrank F (displacementSpace A) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  congr 1
  have h := (fixedSpace A).finrank_quotient_add_finrank
  have hc : Module.finrank F (fixedSpace A) = Module.finrank F (Vector F)-
      Module.finrank F (displacementSpace A) := by
    rw [←orthogonal_displacementSpace,
      LinearMap.BilinForm.finrank_orthogonal form_nondegenerate]
  rw [hc] at h
  have hle := (displacementSpace A).finrank_le
  omega

/-- Every nontrivial inner actor has natural moving index at least four. -/
theorem four_le_fixed_quotient_card
    (hF : Nat.card F = 4) (A : Subgroup (Sp F)) (hA : 1 < Nat.card A) :
    4 ≤ Nat.card (Vector F ⧸ fixedSpace A) := by
  have hc := card_actor_le_displacement_dimension A
  have hd : 1 ≤ Module.finrank F (displacementSpace A) := by
    by_contra hn
    have hz : Module.finrank F (displacementSpace A) = 0 := by omega
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero] at hc
    omega
  rw [fixed_quotient_card,hF]
  exact Nat.pow_le_pow_right (by decide : 0 < 4) hd

/-- Reciprocal centralizer indices exclude every small order except four. -/
theorem reciprocal_small_actor_card_four_of_fields
    {K : Type*} [Field K] [Finite K]
    (hF : Nat.card F=4) (hK : Nat.card K=4) (A : Subgroup (Sp F)) (B : Subgroup (Sp K))
    (hB : 1 < Nat.card B)
    (hAB : Nat.card (Vector F ⧸ fixedSpace A) ≤ Nat.card B)
    (hBA : Nat.card (Vector K ⧸ fixedSpace B) ≤ Nat.card A)
    (hsmall : Nat.card A < 16) :
    Nat.card A=4 ∧ Nat.card B=4 ∧
      Module.finrank F (displacementSpace A)=1 ∧
      Module.finrank K (displacementSpace B)=1 := by
  have hAc := card_actor_le_displacement_dimension A
  have hBc := card_actor_le_displacement_dimension B
  rw [fixed_quotient_card,hF] at hAB
  rw [fixed_quotient_card,hK] at hBA
  rw [hF] at hAc
  rw [hK] at hBc
  have hdB : Module.finrank K (displacementSpace B) ≤ 1 := by
    by_contra h
    have hd : 2 ≤ Module.finrank K (displacementSpace B) := by omega
    have hh := Nat.pow_le_pow_right (by decide : 0 < 4) hd
    omega
  have hdB' : Module.finrank K (displacementSpace B)=1 := by
    interval_cases hh : Module.finrank K (displacementSpace B) <;> simp at hBc <;> omega
  rw [hdB'] at hBc hBA
  norm_num at hBc hBA
  have hdA : Module.finrank F (displacementSpace A) ≤ 1 := by
    by_contra h
    have hd : 2 ≤ Module.finrank F (displacementSpace A) := by omega
    have hh := Nat.pow_le_pow_right (by decide : 0 < 4) hd
    omega
  have hdA' : Module.finrank F (displacementSpace A)=1 := by
    interval_cases hh : Module.finrank F (displacementSpace A) <;> simp at hAc <;> omega
  rw [hdA'] at hAc hAB
  norm_num at hAc hAB
  exact ⟨by omega,by omega,hdA',hdB'⟩

theorem reciprocal_small_actor_card_four
    (hF : Nat.card F=4) (A B : Subgroup (Sp F))
    (hB : 1 < Nat.card B)
    (hAB : Nat.card (Vector F ⧸ fixedSpace A) ≤ Nat.card B)
    (hBA : Nat.card (Vector F ⧸ fixedSpace B) ≤ Nat.card A)
    (hsmall : Nat.card A < 16) :
    Nat.card A=4 ∧ Nat.card B=4 ∧
      Module.finrank F (displacementSpace A)=1 ∧
      Module.finrank F (displacementSpace B)=1 :=
  reciprocal_small_actor_card_four_of_fields hF hF A B hB hAB hBA hsmall

omit [Finite F] in
/-- The literal centralizer maps into the fixed space of an equivariant quotient. -/
theorem fixed_quotient_card_le_centralizer_index
    {G : Type*} [Group G] (U A : Subgroup G) [Finite U]
    (hn : A ≤ normalizer (U : Set G))
    (π : U →* Multiplicative (Vector F)) (hp : Function.Surjective π)
    (α : A →* Sp F)
    (hact : ∀ (a : A) (u : U),
      π ⟨a.val*u.val*a.val⁻¹,(mem_normalizer_iff.mp (hn a.property) u).mp u.property⟩ =
        Multiplicative.ofAdd (α a • (π u).toAdd)) :
    Nat.card (Vector F ⧸ fixedSpace α.range) ≤ (centralizer (A : Set G)).relIndex U := by
  let f : U →* Multiplicative (Vector F ⧸ fixedSpace α.range) :=
    (fixedSpace α.range).mkQ.toAddMonoidHom.toMultiplicative.comp π
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := (fixedSpace α.range).mkQ_surjective v.toAdd
    obtain ⟨u,hu⟩ := hp (Multiplicative.ofAdd w)
    refine ⟨u,?_⟩
    change Multiplicative.ofAdd ((fixedSpace α.range).mkQ (π u).toAdd)=v
    rw [hu,toAdd_ofAdd,hw,ofAdd_toAdd]
  have hker : (centralizer (A : Set G)).subgroupOf U ≤ f.ker := by
    intro u hu
    change (fixedSpace α.range).mkQ (π u).toAdd=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rintro g ⟨a,rfl⟩
    have hconj : a.val*u.val*a.val⁻¹=u.val := by
      have hc : a.val*u.val=u.val*a.val := hu a.val a.property
      rw [hc,mul_inv_cancel_right]
    have hh := hact a u
    have he : (⟨a.val*u.val*a.val⁻¹,
      (mem_normalizer_iff.mp (hn a.property) u).mp u.property⟩ : U)=u := Subtype.ext hconj
    rw [he] at hh
    exact congrArg Multiplicative.toAdd hh.symm
  have hidx : f.ker.index = Nat.card (Vector F ⧸ fixedSpace α.range) := by
    rw [index_ker,f.range_eq_top_of_surjective hf]
    exact Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative (Vector F ⧸ fixedSpace α.range))) ≃* _).toEquiv
  rw [←hidx]
  change f.ker.index ≤ ((centralizer (A : Set G)).subgroupOf U).index
  have h := relIndex_le_of_le_left (L := (⊤ : Subgroup U)) hker index_ne_zero_of_finite
  simpa only [relIndex_top_right] using h
end Theory.SpecificGroups.SymplecticFour
