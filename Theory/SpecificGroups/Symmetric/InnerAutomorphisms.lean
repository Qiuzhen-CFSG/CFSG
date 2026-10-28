module

public import Theory.Alternating.Aut

/-!
# Inner automorphisms of symmetric groups outside degree six

Restriction to the characteristic alternating subgroup is injective, since
its conjugation action detects permutations. The proved alternating-group
automorphism theorem supplies a permutation inducing any restricted
automorphism. Injectivity then proves the original automorphism is inner.

Source: GLS3, Theorem 5.2.1. The degree-seven case places the actual ambient
actor after the normal-closure sieve in Aschbacher–Smith, C.5.12 and G.6.4.
-/

public section

open Subgroup
namespace Equiv.Perm

theorem alternating_restriction_injective {n : ℕ} (hn : 5 ≤ n) (h6 : n ≠ 6) :
    Function.Injective (MulAut.characteristic (alternatingGroup (Fin n))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  have hfq (q : alternatingGroup (Fin n)) : f (q : Equiv.Perm (Fin n)) = q :=
    congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hf) q)
  apply MulEquiv.ext
  intro p
  apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6).injective
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  change f p * (q : Equiv.Perm (Fin n)) * (f p)⁻¹ =
    p * (q : Equiv.Perm (Fin n)) * p⁻¹
  calc
    _ = f (p * (q : Equiv.Perm (Fin n)) * p⁻¹) := by
      rw [map_mul, map_mul, map_inv, hfq q]
    _ = _ := hfq (MulAut.conjNormal p q)

theorem conj_surjective_of_degree {n : ℕ} (hn : 5 ≤ n) (h6 : n ≠ 6) :
    Function.Surjective (MulAut.conj : Equiv.Perm (Fin n) →* MulAut (Equiv.Perm (Fin n))) := by
  intro f
  obtain ⟨p, hp⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6).surjective
    (MulAut.characteristic (alternatingGroup (Fin n)) f)
  refine ⟨p, alternating_restriction_injective hn h6 ?_⟩
  exact hp
end Equiv.Perm
