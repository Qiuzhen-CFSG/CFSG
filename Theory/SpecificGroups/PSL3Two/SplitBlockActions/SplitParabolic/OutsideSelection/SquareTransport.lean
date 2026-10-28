module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionTypes

/-!
# Transport of the a₂ condition on the actual central square quotient

An equivariant group isomorphism induces an equivalence of the quotients
by their centers, of their fixed subgroups, and of their square maps.
Consequently it preserves the a₂ condition: an involutory quotient action,
a fixed plane of order four, and square one on that plane. The equivalence
is compatible with the literal quotient maps on every representative.

This is used to return the unitriangular involution calculation to the
actual first-parabolic two-core, keeping the original conjugation action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Definition
E.2.6, printed p.218, and proof of 14.4.4, printed p.1007.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Two.SplitParabolic.OutsideSelection

variable {P Q : Type*} [Group P] [Group Q]

private theorem center_map (e : P ≃* Q) : (center P).map e.toMonoidHom = center Q := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (centerCongr e ⟨y,hy⟩).property
  · intro hx
    refine ⟨((centerCongr e).symm ⟨x,hx⟩ : P),
      ((centerCongr e).symm ⟨x,hx⟩).property, ?_⟩
    exact congrArg Subtype.val ((centerCongr e).apply_symm_apply ⟨x,hx⟩)

/-- The center quotient, with the actual quotient maps retained. -/
def centerQuotientEquiv (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr (center P) (center Q) e (by exact center_map e)

theorem centerQuotientEquiv_mk (e : P ≃* Q) (x : P) :
    centerQuotientEquiv e (QuotientGroup.mk' (center P) x) =
      QuotientGroup.mk' (center Q) (e x) := rfl

variable [Finite P] [Finite Q]

/-- Equivariant transport of the square-quotient a₂ condition. -/
theorem a2_transport (dP : QuaternionCentralProductData P)
    (dQ : QuaternionCentralProductData Q) (e : P ≃* Q)
    (α : MulAut P) (β : MulAut Q) (he : ∀ x, e (α x) = β (e x))
    (ha : dP.IsA2Action α) : dQ.IsA2Action β := by
  let f := centerQuotientEquiv e
  have hf : ∀ v, f (quotientAut (center P) α v) = quotientAut (center Q) β (f v) := by
    intro v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    rw [quotientAut_apply_mk]
    simp only [f, centerQuotientEquiv_mk, quotientAut_apply_mk, he]
  have hm : (dP.fixedSquareQuotient α).map f.toMonoidHom = dQ.fixedSquareQuotient β := by
    ext v
    obtain ⟨w,rfl⟩ := f.surjective v
    refine (mem_map_iff_mem (f := f.toMonoidHom) f.injective).trans ?_
    change quotientAut (center P) α w = w ↔
      quotientAut (center Q) β (f w) = f w
    rw [← hf, f.injective.eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply MulEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := f.surjective v
    have hh := DFunLike.congr_fun ha.1 w
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at hh ⊢
    rw [← hf, ← hf, hh]
  · rw [← hm, card_map_of_injective (f := f.toMonoidHom) f.injective]
    exact ha.2.1
  · intro v hv
    obtain ⟨w,rfl⟩ := f.surjective v
    have hw : w ∈ dP.fixedSquareQuotient α := by
      rw [← mem_map_iff_mem (f := f.toMonoidHom) f.injective, hm]
      exact hv
    have hs := ha.2.2 w hw
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) w
    apply Subtype.ext
    change (dQ.square (f (QuotientGroup.mk' (center P) x)) : Q) = 1
    rw [show f (QuotientGroup.mk' (center P) x) =
      QuotientGroup.mk' (center Q) (e x) from rfl, dQ.square_mk, ← map_pow]
    have hs' : x^2=1 := by
      simpa only [dP.square_mk, Subgroup.coe_one] using congrArg Subtype.val hs
    rw [hs', map_one]

end Matrix.PSL3Two.SplitParabolic.OutsideSelection
