module
public import Theory.SpecificGroups.SymmetricFiveInvolutions
/-!
# Order-four elements centralizing a transposition in S₅

The centralizer of a transposition is C₂ × S₃, so its elements whose
fourth power is one already have square one. Conjugate to the transposition
(0 1) and check its 120 possible centralizing permutations in the kernel.
This sends order-four squares into the extraspecial core in the terminal
centralizer argument of Aschbacher–Smith 14.2.17(1), printed p.987.
-/
public section
namespace Equiv.Perm
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem swap_zero_one_square : ∀ b : Perm (Fin 5),
    b * Equiv.swap 0 1 = Equiv.swap 0 1 * b → b^4=1 → b^2=1 := by decide +kernel

public theorem square_eq_one_of_commute_swap_of_pow_four
    (a : Perm (Fin 5)) (ha : a.IsSwap) (b : Perm (Fin 5))
    (hb : Commute b a) (hb4 : b^4=1) : b^2=1 := by
  obtain ⟨i,j,hij,rfl⟩ := ha
  obtain ⟨g,hg⟩ := isConj_iff.mp (isConj_swap hij (by decide : (0:Fin 5) ≠ 1))
  let f : Perm (Fin 5) ≃* Perm (Fin 5) := MulAut.conj g
  have hf : f (Equiv.swap i j) = Equiv.swap 0 1 := hg
  have hcomm : Commute (f b) (Equiv.swap 0 1) := hf ▸ hb.map f.toMonoidHom
  have h4 : (f b)^4=1 := by rw [←map_pow,hb4,map_one]
  apply f.injective
  simpa only [map_pow,map_one] using swap_zero_one_square (f b) hcomm.eq h4
end Equiv.Perm
