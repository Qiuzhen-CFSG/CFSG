module

public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.NormalClosure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A simultaneous inverter above the full residual of S₃ × S₃

If a subgroup of a Sylow two-subgroup moves the whole odd residual, both
coordinate projections of that subgroup are nontrivial. Its multiplication
then supplies an involution nontrivial on both coordinates, and this
involution inverts the entire residual. The residual itself is identified
with the product of two cyclic groups of order three. All finite checks
are confined to individual permutations of three points.

Application: the order-nine image branch of Aschbacher--Smith 15.2.3(1),
printed pp.1104--1105, via the literal intersection-core action image.
-/

public section
open Subgroup
open scoped commutatorElement
namespace SymmetricThreeProductResidual

private theorem model_square_of_fourth : ∀ r : SymmetricThreeProduct.S3, r ^ 4 = 1 → r ^ 2 = 1 := by
  decide +kernel

private theorem coordinate_inverts : ∀ r y : SymmetricThreeProduct.S3, r ^ 2 = 1 → r ≠ 1 →
    y ∈ alternatingGroup (Fin 3) → r * y * r⁻¹ = y⁻¹ := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem model_inverter (R : Subgroup SymmetricThreeProduct.G)
    (hsq : ∀ r ∈ R, r ^ 2 = 1)
    (hfull : ⁅pResidual 2 SymmetricThreeProduct.G,R⁆ = pResidual 2 SymmetricThreeProduct.G) :
    ∃ r : SymmetricThreeProduct.G, r ∈ R ∧ orderOf r = 2 ∧
      ∀ y ∈ pResidual 2 SymmetricThreeProduct.G, r * y * r⁻¹ = y⁻¹ := by
  classical
  have hleft : ∃ r ∈ R, r.1 ≠ 1 := by
    by_contra! hn
    have hR : R ≤ (MonoidHom.fst SymmetricThreeProduct.S3 SymmetricThreeProduct.S3).ker := fun r hr => hn r hr
    have hc := (commutator_mono (le_refl (pResidual 2 SymmetricThreeProduct.G)) hR).trans
      (commutator_le_right _ _)
    rw [hfull, SymmetricThreeProductResidual.residual_eq] at hc
    have h := hc (show ((Equiv.swap 0 1 * Equiv.swap 1 2 : SymmetricThreeProduct.S3), 1) ∈
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) by
        simp only [Subgroup.mem_prod, Equiv.Perm.mem_alternatingGroup]
        decide +kernel)
    change (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 1 at h
    have hn' : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ≠ 1 := by decide +kernel
    exact hn' h
  have hright : ∃ r ∈ R, r.2 ≠ 1 := by
    by_contra! hn
    have hR : R ≤ (MonoidHom.snd SymmetricThreeProduct.S3 SymmetricThreeProduct.S3).ker := fun r hr => hn r hr
    have hc := (commutator_mono (le_refl (pResidual 2 SymmetricThreeProduct.G)) hR).trans
      (commutator_le_right _ _)
    rw [hfull, SymmetricThreeProductResidual.residual_eq] at hc
    have h := hc (show (1, (Equiv.swap 0 1 * Equiv.swap 1 2 : SymmetricThreeProduct.S3)) ∈
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) by
        simp only [Subgroup.mem_prod, Equiv.Perm.mem_alternatingGroup]
        decide +kernel)
    change (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 1 at h
    have hn' : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ≠ 1 := by decide +kernel
    exact hn' h
  have hboth : ∃ r ∈ R, r.1 ≠ 1 ∧ r.2 ≠ 1 := by
    obtain ⟨r,hr,hr1⟩ := hleft
    obtain ⟨s,hs,hs2⟩ := hright
    by_cases hr2 : r.2 = 1
    · by_cases hs1 : s.1 = 1
      · exact ⟨r*s, R.mul_mem hr hs, by simpa [hs1], by simpa [hr2]⟩
      · exact ⟨s,hs,hs1,hs2⟩
    · exact ⟨r,hr,hr1,hr2⟩
  obtain ⟨r,hr,hr1,hr2⟩ := hboth
  refine ⟨r,hr,orderOf_eq_prime_iff.mpr ⟨hsq r hr, ?_⟩, ?_⟩
  · intro he
    exact hr1 (congrArg Prod.fst he)
  · intro y hy
    rw [SymmetricThreeProductResidual.residual_eq] at hy
    apply Prod.ext
    · exact coordinate_inverts r.1 y.1 (congrArg Prod.fst (hsq r hr)) hr1 hy.1
    · exact coordinate_inverts r.2 y.2 (congrArg Prod.snd (hsq r hr)) hr2 hy.2

/-- Full movement of the odd residual forces a simultaneous inverter in the actor. -/
theorem exists_full_residual_inverter {X : Type*} [Group X]
    (e : X ≃* SymmetricThreeProduct.G) (P : Sylow 2 X) (R : Subgroup X)
    (hle : R ≤ (P : Subgroup X)) (hfull : ⁅pResidual 2 X,R⁆ = pResidual 2 X) :
    ∃ r : X, r ∈ R ∧ orderOf r = 2 ∧
      ∀ y ∈ pResidual 2 X, r * y * r⁻¹ = y⁻¹ := by
  let : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hX : Nat.card X = 36 := (Nat.card_congr e.toEquiv).trans SymmetricThreeProduct.card_group
  have hP : Nat.card P = 4 := by rw [P.card_eq_multiplicity,hX]; decide +kernel
  have hsq : ∀ r ∈ R.map e.toMonoidHom, r ^ 2 = 1 := by
    rintro _ ⟨r,hr,rfl⟩
    have hp : r ^ 4 = 1 := by
      exact congrArg Subtype.val (hP ▸ pow_card_eq_one' (x := (⟨r,hle hr⟩ : P)))
    have he : e r ^ 4 = 1 := by rw [← map_pow,hp,map_one]
    exact Prod.ext (model_square_of_fourth _ (congrArg Prod.fst he))
      (model_square_of_fourth _ (congrArg Prod.snd he))
  have hfull' : ⁅pResidual 2 SymmetricThreeProduct.G,R.map e.toMonoidHom⁆ = pResidual 2 SymmetricThreeProduct.G := by
    have h := congrArg (Subgroup.map e.toMonoidHom) hfull
    rwa [map_commutator,map_pResidual_of_surjective 2 _ e.surjective] at h
  obtain ⟨r',hr',ho,hi⟩ := model_inverter _ hsq hfull'
  obtain ⟨r,hr,her⟩ := hr'
  subst r'
  refine ⟨r,hr,?_,fun y hy => ?_⟩
  · simpa using ho
  · apply e.injective
    simp only [map_mul,map_inv]
    apply hi
    rw [← map_pResidual 2 e]
    exact mem_map_of_mem e.toMonoidHom hy

/-- The odd residual has actual elementary-nine coordinates. -/
theorem residual_equiv_elementaryNine {X : Type*} [Group X] (e : X ≃* SymmetricThreeProduct.G) :
    Nonempty ((pResidual 2 X) ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  let a : alternatingGroup (Fin 3) ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq hc (by simp)
  refine ⟨(e.subgroupMap (pResidual 2 X)).trans ?_⟩
  exact ((MulEquiv.subgroupCongr ((map_pResidual 2 e).trans
    SymmetricThreeProductResidual.residual_eq)).trans
      (Subgroup.prodEquiv _ _)).trans (a.prodCongr a)

/-- An order-nine commutator image is the full residual. -/
theorem commutator_eq_residual_of_card_nine {D : Type*} [Group D]
    (e : D ≃* SymmetricThreeProduct.G) (R : Subgroup D)
    (hc : Nat.card (⁅pResidual 2 D,R⁆ : Subgroup D) = 9) :
    ⁅pResidual 2 D,R⁆ = pResidual 2 D := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨a⟩ := residual_equiv_elementaryNine e
  have hA : Nat.card (pResidual 2 D) = 9 := by
    rw [Nat.card_congr a.toEquiv]
    simp
  apply eq_of_le_of_card_ge (commutator_le_left _ _)
  rw [hA,hc]

/-- The order-nine normal-closure residual supplies its inverter in the original subgroup. -/
theorem normalClosure_residual_inverter_of_card_nine {D : Type*} [Group D]
    (e : D ≃* SymmetricThreeProduct.G) (P : Sylow 2 D) (R : Subgroup D)
    (hle : R ≤ (P : Subgroup D))
    (hc : Nat.card ((pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype) = 9) :
    ∃ r : D, r ∈ R ∧ orderOf r = 2 ∧
      ∀ y ∈ pResidual 2 D, r * y * r⁻¹ = y⁻¹ := by
  apply exists_full_residual_inverter e P R hle
  rw [← normalClosure_residual_eq_commutator e P R hle]
  exact normalClosure_residual_eq_of_card_nine e R hc

end SymmetricThreeProductResidual
