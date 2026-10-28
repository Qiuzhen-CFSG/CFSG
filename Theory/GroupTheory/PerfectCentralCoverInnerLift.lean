module
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Innerness lifted through a perfect central cover

If a compatible quotient automorphism is inner, lift its conjugating element.
Uniqueness of maps from a perfect group through a central extension identifies
the original automorphism with this inner lift. No assumption on the size or
structure of the central kernel is needed.

Source: the standard perfect central-cover uniqueness argument, used in
Aschbacher–Smith 15.3.21, printed p.1127.
-/
public section
namespace PerfectCentralCovering
theorem Cover.inner_of_equivariant_inner {E B : Type*} [Group E] [Group B]
    (f : Cover E B) (a : MulAut E) (b : MulAut B)
    (he : ∀ x, f.toMonoidHom (a x) = b (f.toMonoidHom x))
    (hb : ∃ y, b = MulAut.conj y) : ∃ x, a = MulAut.conj x := by
  let := f.isPerfect
  obtain ⟨y,rfl⟩ := hb
  obtain ⟨x,hx⟩ := f.surjective y
  refine ⟨x, MulEquiv.toMonoidHom_injective ?_⟩
  apply monoidHom_eq_of_isPerfect_of_comp_eq f.toMonoidHom f.ker_le_center
  ext z
  change f.toMonoidHom (a z) = f.toMonoidHom (x * z * x⁻¹)
  rw [he,map_mul,map_mul,map_inv,hx]
  rfl
end PerfectCentralCovering
