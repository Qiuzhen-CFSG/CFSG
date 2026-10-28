module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# Detecting symmetric automorphisms on A₆

Restriction from Aut(S₆) to Aut(A₆) is injective: an automorphism trivial on
A₆ preserves the conjugation action of each permutation, and the natural
permutation action on A₆ is faithful. A subgroup of Aut(A₆) strictly
containing the natural S₆ is the whole group, by its proved index two.

These facts provide the compatible action step in Aschbacher,
“A 2-local characterization of M12”, Lemma 4.8, p.41.
-/

@[expose] public section

open Subgroup
namespace AlternatingSix.ShadowLocal

def symmetricRestriction : MulAut (Equiv.Perm (Fin 6)) →* AutA6 :=
  MulAut.characteristic A6

theorem symmetricRestriction_injective : Function.Injective symmetricRestriction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  have hfq (q : A6) : f (q : Equiv.Perm (Fin 6)) = q :=
    congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hf) q)
  apply MulEquiv.ext
  intro p
  apply permutationAction_injective
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  change f p * (q : Equiv.Perm (Fin 6)) * (f p)⁻¹ =
    p * (q : Equiv.Perm (Fin 6)) * p⁻¹
  calc
    _ = f (p * (q : Equiv.Perm (Fin 6)) * p⁻¹) := by
      rw [map_mul, map_mul, map_inv, hfq q]
    _ = _ := hfq (permutationAction p q)

theorem symmetricRestriction_conj (p : Equiv.Perm (Fin 6)) :
    symmetricRestriction (MulAut.conj p) = permutationAction p := by
  ext q : 2
  rfl

/-- A subgroup containing the natural symmetric group and an element outside it
is the whole automorphism group. -/
theorem eq_top_of_natural_lt {R : Subgroup AutA6} (h : natural < R) : R = ⊤ := by
  have hd := index_dvd_of_le h.le
  rw [GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact index_eq_one.mp h1
  · have hr := relIndex_mul_index h.le
    rw [h2, GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index] at hr
    have hn : natural.relIndex R = 1 := by omega
    exact (h.not_ge (relIndex_eq_one.mp hn)).elim

end AlternatingSix.ShadowLocal
