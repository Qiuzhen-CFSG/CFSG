module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
public import Theory.GroupTheory.PResidual.NontrivialImage
public import Theory.GroupTheory.PResidual.NormalClosureCommutator

/-!
# Normal-closure residuals in a symmetric-three square

The two-residual of S₃×S₃ has order nine, and its two-core is trivial.
Thus the residual of the normal closure of a nontrivial subgroup has
order three or nine: if trivial, that normal closure would be a normal
two-subgroup. An order-nine residual is the entire ambient two-residual.

Application: the actual intersection-core image in Aschbacher--Smith
15.2.3(1),(3), printed pp.1104--1105. This is the image dichotomy, not
an identification of the central extension above that image.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace SymmetricThreeProductResidual
variable {D : Type*} [Group D]

private theorem transported_residual_card
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Nat.card (pResidual 2 D) = 9 := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have h := map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
  have hc := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) => Nat.card H) h
  rw [card_map_of_injective e.injective, residual_card] at hc
  exact hc

private theorem transported_core
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    pCore 2 D = ⊥ := by
  have hn : ((pCore 2 D).map e.toMonoidHom).Normal :=
    (inferInstance : (pCore 2 D).Normal).map _ e.surjective
  have hh : (pCore 2 D).map e.toMonoidHom ≤
      pCore 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  rw [SymmetricThreeProduct.twoCore_eq_bot] at hh
  exact (map_eq_bot_iff_of_injective _ e.injective).mp (bot_unique hh)

/-- A nontrivial normal closure has nontrivial two-residual of order three or nine. -/
theorem normalClosure_residual_card
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (R : Subgroup D) (hne : R ≠ ⊥) :
    Nat.card ((pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype) = 3 ∨
    Nat.card ((pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype) = 9 := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  let N := normalClosure (R : Set D)
  let K := (pResidual 2 N).map N.subtype
  have hN : N ≠ ⊥ := fun he => hne (bot_unique (le_normalClosure.trans he.le))
  have hK : K ≠ ⊥ := by
    have hh := embedded_pResidual_image_ne_bot_of_pCore_eq_bot 2 N
      (MonoidHom.id D) Function.surjective_id (transported_core e)
      (by simpa only [Subgroup.map_id] using hN)
    simpa only [Subgroup.map_id] using hh
  have hd : Nat.card K ∣ 9 := by
    rw [← transported_residual_card e]
    exact card_dvd_of_le (map_pResidual_le 2 N.subtype)
  have hpos := Nat.card_pos (α := K)
  have hone : Nat.card K ≠ 1 := fun hc => hK (card_eq_one.mp hc)
  have hle : Nat.card K ≤ 9 := Nat.le_of_dvd (by decide) hd
  change Nat.card K = 3 ∨ Nat.card K = 9
  interval_cases hc : Nat.card K <;> simp_all

/-- The order-nine case is exactly the full ambient two-residual. -/
theorem normalClosure_residual_eq_of_card_nine
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (R : Subgroup D)
    (hcard : Nat.card ((pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype) = 9) :
    (pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype = pResidual 2 D := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  apply eq_of_le_of_card_ge (map_pResidual_le 2 (normalClosure (R : Set D)).subtype)
  rw [hcard, transported_residual_card e]

/-- The literal residual image is the commutator with the odd residual. -/
theorem normalClosure_residual_eq_commutator
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (P : Sylow 2 D) (R : Subgroup D) (hle : R ≤ (P : Subgroup D)) :
    (pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype = ⁅pResidual 2 D, R⁆ := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have hD : Nat.card D = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    decide
  have hP : Nat.card P = 2 ^ 2 := by
    rw [P.card_eq_multiplicity, hD]
    decide +kernel
  let : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP
  have hc : R ≤ centralizer (P : Set D) := by
    intro r hr p hp
    exact congrArg (P : Subgroup D).subtype (mul_comm (⟨p, hp⟩ : P) ⟨r, hle hr⟩)
  apply embedded_twoResidual_normalClosure_eq_commutator
    (pResidual 2 D) (P : Subgroup D) R (pResidual_sup_sylow_eq_top P) _
    (P.isPGroup'.to_le hle) hc
  rw [transported_residual_card e]
  decide

end SymmetricThreeProductResidual
