module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry

/-!
# The field involution acts nontrivially on the covering center

The source Sylow three-subgroup X satisfies C_{S_L}(X)=1, and the field
involution inverts X. If the field involution fixed Z(L) pointwise, each
X-action on Z(L) would equal its inverse. Its order is both odd and at most
two, so X would fix all of the nontrivial center, a contradiction.

The marked-normalizer specialization uses its actual inclusion of X and its
proved inversion formula. Thus no assertion about involution fusion or the
field action on the center is assumed.
Source: Aschbacher--Smith, proof of 15.3.38, printed pp.1136--1137,
combined manuscript of 1 March 2004.
-/

public section

namespace Matrix.PSL3Four.InvolutionClasses
open Subgroup

private theorem center_restriction {E : Type*} [Group E] :
    ∃ r : MulAut E →* MulAut (center E), ∀ a z, (r a z : E) = a (z : E) := by
  exact ⟨{ toFun := centerCongr
           map_one' := MulEquiv.ext fun _ => rfl
           map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl }, fun _ _ => rfl⟩

/-- Inverting an odd subgroup with no common central fixed point moves the center. -/
theorem field_moves_center_of_three_geometry {I : Type*} [Group I]
    {L : Subgroup I} [L.Normal] (c : FourCover L)
    (X : Subgroup I) (hX : IsPGroup 3 X) (f : I)
    (hinv : ∀ x : X, f * (x : I) * f⁻¹ = (x : I)⁻¹)
    (hfree : ((center L).map L.subtype) ⊓ centralizer (X : Set I) = ⊥) :
    ∃ z : center L, f * ((z : L) : I) * f⁻¹ ≠ ((z : L) : I) := by
  obtain ⟨r, hr⟩ := center_restriction (E := L)
  let a : I →* MulAut (center L) := r.comp MulAut.conjNormal
  by_contra! hf
  have haf : a f = 1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change ((r (MulAut.conjNormal f) z : L) : I) = ((z : L) : I)
    rw [hr]
    exact hf z
  have hax (x : X) : a (x : I) = 1 := by
    have he : a (x : I) = (a (x : I))⁻¹ := by
      have h := congrArg a (hinv x)
      simpa only [map_mul, map_inv, haf, inv_one, one_mul, mul_one] using h
    have hs : (a (x : I)) ^ 2 = 1 := by
      calc
        _ = (a (x : I))⁻¹ * a (x : I) := by
          rw [pow_two]
          exact congrArg (fun b => b * a (x : I)) he
        _ = 1 := inv_mul_cancel _
    have hcop : (orderOf (a (x : I))).Coprime 2 :=
      (hX.orderOf_coprime (by decide) x).of_dvd_left (orderOf_map_dvd (a.comp X.subtype) x)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (orderOf_dvd_of_pow_eq_one hs))
  let : IsKleinFour (center L) := c.center_isKleinFour
  let : Nontrivial (center L) := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let := hs
    have he := Nat.card_unique (α := center L)
    simp only [IsKleinFour.card_four] at he
    contradiction)
  obtain ⟨z, hz⟩ := exists_ne (1 : center L)
  have hzC : ((z : L) : I) ∈ centralizer (X : Set I) := by
    intro x hx
    have he := DFunLike.congr_fun (hax ⟨x, hx⟩) z
    have hev := congrArg (fun t : center L => ((t : L) : I)) he
    change ((r (MulAut.conjNormal x) z : L) : I) = ((z : L) : I) at hev
    rw [hr] at hev
    change x * ((z : L) : I) * x⁻¹ = ((z : L) : I) at hev
    exact mul_inv_eq_iff_eq_mul.mp hev
  have he : ((z : L) : I) = 1 :=
    mem_bot.mp (hfree ▸ (show ((z : L) : I) ∈ _ ⊓ centralizer (X : Set I) from
      ⟨mem_map_of_mem L.subtype z.property, hzC⟩))
  exact hz (Subtype.ext (Subtype.ext he))

end Matrix.PSL3Four.InvolutionClasses

namespace Matrix.PSL3Four.InvolutionClasses
open Subgroup ExtendedCentralizer

/-- Apply the three-subgroup argument to the selected source normalizer. -/
theorem normalizer_field_moves_center_of_fixed_free {I : Type*} [Group I]
    {L : Subgroup I} [L.Normal] {d : Overgroup L} (n : NormalizerGeometry d)
    (hfree : ((center L).map L.subtype) ⊓
      centralizer (((n.X : Subgroup n.YS).map n.YS.subtype) : Set I) = ⊥) :
    ∃ z : center L, n.fieldI * ((z : L) : I) * n.fieldI⁻¹ ≠ ((z : L) : I) := by
  apply field_moves_center_of_three_geometry d.cover
    ((n.X : Subgroup n.YS).map n.YS.subtype) (n.X.isPGroup'.map n.YS.subtype)
    n.fieldI _ hfree
  rintro ⟨x, y, hy, rfl⟩
  exact n.field_inverts_three ⟨y, (n.X : Subgroup n.YS).le_normalizer hy⟩ hy

end Matrix.PSL3Four.InvolutionClasses
