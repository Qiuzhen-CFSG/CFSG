module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.Contracts
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Nineteen involutions in the actual quaternion central product

Multiplication of the two quaternion factors constructs a surjection from
Q₈ × Q₈ with the diagonal central involution as its exact kernel. Choosing
one of each pair of quaternion signs gives unique representatives. Nineteen
of those representatives are nonidentity square-one elements in the quotient.
Only the 64-element cover is enumerated; the ambient group is arbitrary.

The source hypotheses construct the two quaternion factors, so the final
count has no model, presentation or counting premise.
Source: Aschbacher, “A 2-local characterization of M12”, proof of Lemma 2.3,
printed p.34. The cover follows the existing construction in
Theory/GroupTheory/QuaternionCentralProductInvolutionCentralizers.lean.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
private abbrev Pair := QuaternionGroup 2 × QuaternionGroup 2
private abbrev diagonal : Pair := (QuaternionGroup.a 2, QuaternionGroup.a 2)
private abbrev diagonalKernel (p : Pair) : Prop := p = 1 ∨ p = diagonal
private def Representative (p : Pair) : Prop :=
  match p.1 with
  | .a n => n.val < 2
  | .xa n => n.val < 2
private instance (p : Pair) : Decidable (Representative p) := by
  unfold Representative
  split <;> infer_instance
private theorem representatives_cover : ∀ p : Pair,
    ∃ q : Pair, Representative q ∧ diagonalKernel (q * p⁻¹) := by decide +kernel
private theorem representatives_unique : ∀ p q : Pair,
    Representative p → Representative q → diagonalKernel (p * q⁻¹) → p = q := by decide +kernel
private theorem representatives_involution_card :
    Fintype.card {p : Pair // Representative p ∧ diagonalKernel (p^2) ∧ ¬diagonalKernel p} = 19 := by
  decide +kernel

private theorem cover_involution_card {L : Type*} [Group L]
    (f : Pair →* L) (hf : Function.Surjective f)
    (hk : ∀ p, f p = 1 ↔ diagonalKernel p) :
    Nat.card {x : L // orderOf x = 2} = 19 := by
  classical
  let R := {p : Pair // Representative p ∧ diagonalKernel (p^2) ∧ ¬diagonalKernel p}
  have hrel (a b : Pair) : f a = f b ↔ diagonalKernel (a * b⁻¹) := by
    rw [← hk, map_mul, map_inv, mul_inv_eq_one]
  let φ : R → {x : L // orderOf x = 2} := fun p => ⟨f p,
    orderOf_eq_prime (by rw [← map_pow]; exact (hk _).mpr p.property.2.1)
      (fun he => p.property.2.2 ((hk _).mp he))⟩
  have hinj : Function.Injective φ := by
    intro p q he
    apply Subtype.ext
    exact representatives_unique p q p.property.1 q.property.1
      ((hrel _ _).mp (congrArg Subtype.val he))
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨p, hp⟩ := hf x
    obtain ⟨q, hq, hqp⟩ := representatives_cover p
    have hqx : f q = x := ((hrel q p).mpr hqp).trans hp
    have hq2 : diagonalKernel (q^2) := (hk _).mp (by
      rw [map_pow, hqx]
      simpa only [x.property] using pow_orderOf_eq_one x.val)
    have hqn : ¬ diagonalKernel q := by
      intro hqk
      have hx1 : x.val = 1 := hqx.symm.trans ((hk _).mpr hqk)
      have hx2 := x.property
      simp [hx1] at hx2
    exact ⟨⟨q, hq, hq2, hqn⟩, Subtype.ext hqx⟩
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm.trans
    ((Nat.card_eq_fintype_card).trans representatives_involution_card)

private theorem quaternion_product_cover {L : Type*} [Group L] [Finite L]
    (d : QuaternionCentralProductData L) :
    ∃ f : Pair →* L, Function.Surjective f ∧ ∀ p, f p = 1 ↔ diagonalKernel p := by
  classical
  let eB := d.left_model.some
  let eC := d.right_model.some
  let fB : QuaternionGroup 2 →* L := d.left.subtype.comp eB.symm.toMonoidHom
  let fC : QuaternionGroup 2 →* L := d.right.subtype.comp eC.symm.toMonoidHom
  let f : Pair →* L := fB.noncommCoprod fC (fun a b =>
    show Commute (fB a) (fC b) from d.commute _ (eB.symm a).property _ (eC.symm b).property)
  have hfB : fB.range = d.left := by
    dsimp [fB]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eB.symm.surjective,
      ← MonoidHom.range_eq_map, d.left.range_subtype]
  have hfC : fC.range = d.right := by
    dsimp [fC]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eC.symm.surjective,
      ← MonoidHom.range_eq_map, d.right.range_subtype]
  have hfrange : f.range = ⊤ := by
    dsimp [f]
    rw [MonoidHom.noncommCoprod_range, hfB, hfC, d.span]
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp hfrange
  obtain ⟨w, hwne, _⟩ :=
    (Nat.card_eq_two_iff' (1 : (d.left ⊓ d.right : Subgroup L))).mp d.intersection_card
  have hw2 : (w : L)^2 = 1 := by
    have hh := pow_card_eq_one' (x := w)
    rw [d.intersection_card] at hh
    exact congrArg Subtype.val hh
  let wb : d.left := ⟨w, w.property.1⟩
  let wc : d.right := ⟨w, w.property.2⟩
  have hwbne : wb ≠ 1 := fun he => hwne (Subtype.ext (congrArg (fun b : d.left => (b : L)) he))
  have hwcne : wc ≠ 1 := fun he => hwne (Subtype.ext (congrArg (fun c : d.right => (c : L)) he))
  have heB : eB wb = QuaternionGroup.a 2 :=
    QuaternionGroup.eq_a_two_of_orderOf_eq_two _ (by
      rw [eB.orderOf_eq]
      exact orderOf_eq_prime (Subtype.ext hw2) hwbne)
  have heC : eC wc = QuaternionGroup.a 2 :=
    QuaternionGroup.eq_a_two_of_orderOf_eq_two _ (by
      rw [eC.orderOf_eq]
      exact orderOf_eq_prime (Subtype.ext hw2) hwcne)
  have hfb : fB (QuaternionGroup.a 2) = w := by
    change ((eB.symm (QuaternionGroup.a 2) : d.left) : L) = w
    rw [← heB, eB.symm_apply_apply]
  have hfc : fC (QuaternionGroup.a 2) = w := by
    change ((eC.symm (QuaternionGroup.a 2) : d.right) : L) = w
    rw [← heC, eC.symm_apply_apply]
  have hdiag : f diagonal = 1 := by
    change fB (QuaternionGroup.a 2) * fC (QuaternionGroup.a 2) = 1
    rw [hfb, hfc, ← pow_two, hw2]
  have hkerCard : Nat.card f.ker = 2 := by
    have hh := f.ker.card_mul_index
    rw [Subgroup.index_ker, hfrange, Nat.card_congr Subgroup.topEquiv.toEquiv, d.card,
      show Nat.card Pair = 64 by rw [Nat.card_eq_fintype_card]; decide] at hh
    omega
  refine ⟨f, hf, ?_⟩
  obtain ⟨k, _, hu⟩ := (Nat.card_eq_two_iff' (1 : f.ker)).mp hkerCard
  have hdiagNe : (⟨diagonal, hdiag⟩ : f.ker) ≠ 1 := by
    intro he
    exact (by decide : diagonal ≠ 1) (congrArg Subtype.val he)
  intro p
  constructor
  · intro hp
    by_cases hp1 : p = 1
    · exact Or.inl hp1
    · exact Or.inr (congrArg Subtype.val
        ((hu ⟨p, hp⟩ (fun he => hp1 (congrArg Subtype.val he))).trans
          (hu ⟨diagonal, hdiag⟩ hdiagNe).symm))
  · rintro (rfl | rfl)
    · exact map_one f
    · exact hdiag

/-- The source core has exactly nineteen involutions. -/
theorem coreInvolutions_card {G : Type*} [Group G] [Finite G] {z : G}
    (h : Hypotheses z) :
    (coreInvolutions z).ncard = 19 := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  let e := (Core z).equivMapOfInjective (Centralizer z).subtype (Centralizer z).subtype_injective
  obtain ⟨f, hf, hk⟩ := quaternion_product_cover (d.map e)
  have hc := cover_involution_card f hf hk
  let e' : {x : coreInG z // orderOf x = 2} ≃ {x : G // x ∈ coreInG z ∧ orderOf x = 2} := {
    toFun x := ⟨x.val, x.val.property, (Subgroup.orderOf_coe x.val).trans x.property⟩
    invFun x := ⟨⟨x, x.property.1⟩, (Subgroup.orderOf_coe (⟨x.val, x.property.1⟩ : coreInG z)).symm.trans x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e').symm.trans hc

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
end
