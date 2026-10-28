module

public import GorensteinWalter.PSL2EvenDefiningKernel
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Perfect central covers of PSL₂(8)

The constructed universal projection onto the actual projective matrix group
PSL₂(F₈) has trivial kernel. The even-field PSL₂ calculation excludes the
defining prime by the scalar action on the root group; cyclic-torus transfer
excludes every odd prime. Consequently every perfect central cover of this
fixed group is an isomorphism. No hypothesis about a module or a two-core
is necessary.

This is the covering calculation used after the exceptional identification
²G₂(3)′ ≃ PSL₂(8). The latter identification is a separate theorem and is
not asserted here. Source: GLS III §6.1, Theorem 6.1.4 and Tables 6.1.2–3;
Aschbacher–Smith I.1.3, printed p.407.
-/

public section

open scoped MatrixGroups
open PerfectCentralCovering

namespace Theory.SpecificGroups.PSL2Eight

/-- The kernel belongs to the constructed universal cover, not to a chosen
matrix projection whose universality is assumed. -/
theorem universalProjection_ker_eq_bot :
    (universalProjection PSL(2, GaloisField 2 3)).ker = ⊥ := by
  have hF : Nat.card (GaloisField 2 3) = 8 := by
    simpa using GaloisField.card 2 3 (by decide)
  let : Fact (3 < Nat.card (GaloisField 2 3)) := ⟨by omega⟩
  have he : Even (Nat.card (GaloisField 2 3)) := by rw [hF]; decide
  apply Subgroup.card_eq_one.mp
  exact GorensteinWalter.PSL2Cover.kernel_card_one_of_even_of_defining_prime_not_dvd
    (GaloisField 2 3) (universalQuasisimpleCover PSL(2, GaloisField 2 3))
    (by omega) he
    (GorensteinWalter.PSL2Cover.defining_prime_not_dvd_universal_kernel_of_even
      (GaloisField 2 3) he (by omega))

/-- Every perfect central cover of the concrete PSL₂(8) has trivial kernel. -/
theorem cover_injective {L : Type*} [Group L]
    (f : Cover L PSL(2, GaloisField 2 3)) : Function.Injective f.toMonoidHom :=
  f.injective_of_universalProjection_ker_eq_bot universalProjection_ker_eq_bot

/-- The given projection itself identifies a perfect cover with PSL₂(8). -/
noncomputable def coverEquiv {L : Type*} [Group L]
    (f : Cover L PSL(2, GaloisField 2 3)) : L ≃* PSL(2, GaloisField 2 3) :=
  MulEquiv.ofBijective f.toMonoidHom ⟨cover_injective f, f.surjective⟩

@[simp] theorem coverEquiv_apply {L : Type*} [Group L]
    (f : Cover L PSL(2, GaloisField 2 3)) (x : L) :
    coverEquiv f x = f.toMonoidHom x := by
  unfold coverEquiv
  rfl

end Theory.SpecificGroups.PSL2Eight
