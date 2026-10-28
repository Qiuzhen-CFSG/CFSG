module
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Embedding a permutation image which acts on two triples

A permutation of `L × Q` whose second coordinate is left multiplication by
one fixed element of `Q` belongs to the regular wreath action of `Perm L ≀ Q`.
The first coordinates, read on each source block and placed at the target
block, explicitly construct the wreath coordinates. This also handles the
interchange of blocks when `Q` has order two.

Consequently, a group action on two numbered triples embeds its permutation
image in `S₃ ≀ C₂`. The proved equivalence `SL₂(2) ≃ S₃` transports the base
coordinates to matrices. The embedding is defined on the actual image;
it requires no faithfulness assumption on the original acting group.
Equal-kernel image equivalences are provided for descent to another image.

This elementary permutation construction is used for the quaternion central
product in Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390.
-/

namespace MonoidHom
/-- Equal kernels identify the two concrete images of a pair of homomorphisms. -/
public noncomputable def rangeEquivOfKerEq {G A B : Type*}
    [Group G] [Group A] [Group B] (f : G →* A) (g : G →* B)
    (h : f.ker = g.ker) : f.range ≃* g.range :=
  (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivRange g))
end MonoidHom

namespace RegularWreathProduct

/-- Numbering the points of a permutation image and realizing its elements in
 a wreath action embeds that image in the wreath product. -/
public theorem exists_embedding_range_of_coordinates
    {A X : Type*} [Group A] (ρ : A →* Equiv.Perm X)
    (e : X ≃ (Fin 3 × Multiplicative (ZMod 2)))
    (h : ∀ a : A, ∃ w : RegularWreathProduct (Equiv.Perm (Fin 3))
        (Multiplicative (ZMod 2)),
      e.permCongrHom (ρ a) = toPerm (Equiv.Perm (Fin 3))
        (Multiplicative (ZMod 2)) (Fin 3) w) :
    ∃ f : ρ.range →* RegularWreathProduct
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)),
      Function.Injective f := by
  let w := toPerm (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)) (Fin 3)
  let c := e.permCongrHom.toMonoidHom.comp ρ.range.subtype
  have hc : ∀ a : ρ.range, c a ∈ w.range := by
    rintro ⟨_, a, rfl⟩
    obtain ⟨b, hb⟩ := h a
    exact ⟨b, hb.symm⟩
  let lift := c.codRestrict w.range hc
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply e.permCongrHom.injective
    exact congrArg Subtype.val hab
  let ew := MonoidHom.ofInjective
    (toPermInj (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)) (Fin 3))
  obtain ⟨es⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let changeBase := congr es.symm (MulEquiv.refl (Multiplicative (ZMod 2)))
  exact ⟨changeBase.toMonoidHom.comp (ew.symm.toMonoidHom.comp lift),
    changeBase.injective.comp (ew.symm.injective.comp hinj)⟩
end RegularWreathProduct

namespace RegularWreathProduct
/-- A permutation which translates all block labels by a fixed group element
is represented by the regular wreath action. -/
public theorem exists_toPerm_eq_of_block_translation
    {L Q : Type*} [Group Q] (p : Equiv.Perm (L × Q)) (q : Q)
    (h : ∀ x : L × Q, (p x).2 = q * x.2) :
    ∃ w : RegularWreathProduct (Equiv.Perm L) Q,
      toPerm (Equiv.Perm L) Q L w = p := by
  have hinv (x : L × Q) : (p.symm x).2 = q⁻¹ * x.2 := by
    have hh := h (p.symm x)
    rw [p.apply_symm_apply] at hh
    rw [hh, inv_mul_cancel_left]
  let f : Q → Equiv.Perm L := fun r =>
    { toFun := fun x => (p (x, q⁻¹ * r)).1
      invFun := fun x => (p.symm (x, r)).1
      left_inv := by
        intro x
        have hh : (p (x, q⁻¹ * r)).2 = r := by rw [h]; simp
        change (p.symm ((p (x, q⁻¹ * r)).1, r)).1 = x
        have hp : ((p (x, q⁻¹ * r)).1, r) = p (x, q⁻¹ * r) :=
          Prod.ext rfl hh.symm
        rw [hp, p.symm_apply_apply]
      right_inv := by
        intro x
        have hh := hinv (x, r)
        change (p ((p.symm (x, r)).1, q⁻¹ * r)).1 = x
        rw [← hh, Prod.eta, p.apply_symm_apply] }
  refine ⟨⟨f, q⟩, ?_⟩
  apply Equiv.ext
  intro x
  change ((f (q * x.2)) x.1, q * x.2) = p x
  apply Prod.ext
  · change (p (x.1, q⁻¹ * (q * x.2))).1 = (p x).1
    simp only [inv_mul_cancel_left, Prod.eta]
  · exact (h x).symm
end RegularWreathProduct

namespace RegularWreathProduct
/-- An action on two numbered triples embeds in `SL₂(2) ≀ C₂` as soon as
all permutations preserve or interchange the two triples. -/
public theorem exists_embedding_range_of_two_blocks
    {A X : Type*} [Group A] (ρ : A →* Equiv.Perm X)
    (e : X ≃ (Fin 3 × Multiplicative (ZMod 2)))
    (h : ∀ a : A, ∃ q : Multiplicative (ZMod 2),
      ∀ x : X, (e (ρ a x)).2 = q * (e x).2) :
    ∃ f : ρ.range →* RegularWreathProduct
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)),
      Function.Injective f := by
  apply exists_embedding_range_of_coordinates ρ e
  intro a
  obtain ⟨q, hq⟩ := h a
  obtain ⟨w, hw⟩ := exists_toPerm_eq_of_block_translation (e.permCongrHom (ρ a)) q (by
    intro y
    change (e (ρ a (e.symm y))).2 = q * y.2
    simpa only [e.apply_symm_apply] using hq (e.symm y))
  exact ⟨w, hw.symm⟩
end RegularWreathProduct
