module
public import Theory.GroupTheory.ZStar.LocalReduction
public import Theory.GroupTheory.WeakClosureQuotient

/-!
# Images of weakly closed involutions

An involution weakly closed in a Sylow two-subgroup remains weakly closed
in the Sylow image under any surjective group homomorphism. No restriction
on the kernel is needed. This gives the odd-core quotient transport used in
Glauberman's Z-star proof, corresponding to the historical branch's
QuotientReduction module.

Apply the existing subgroup weak-closure theorem to the cyclic subgroup
of the involution. Its image is trivial or has order two. In the second
case every conjugation preserving that subgroup fixes its unique nonidentity
element. This reuses the general Sylow-conjugacy transport and avoids
repeating the historical complement construction for the odd-core case.
-/

namespace Glauberman.ZStar
open BenderSuzuki.PFAppendixIII

/-- Surjective images preserve elementwise weak closure of a Sylow involution. -/
public theorem IsWeaklyClosedInSylow.map
    {G H : Type*} [Group G] [Finite G] [Group H]
    (S : Sylow 2 G) {t : G} (ht : IsInvolution t)
    (hweak : IsWeaklyClosedInSylow t (S : Subgroup G))
    (q : G →* H) (hq : Function.Surjective q) :
    IsWeaklyClosedInSylow (q t) ((S : Subgroup G).map q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJS : Subgroup.zpowers t ≤ (S : Subgroup G) :=
    Subgroup.zpowers_le.mpr hweak.1
  have hJweak (g : G)
      (hg : (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G)) :
      (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers t := by
    have hm := hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
      (Subgroup.mem_zpowers t))
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (hweak.2 g hm)
  refine ⟨Subgroup.mem_map_of_mem q hweak.1, ?_⟩
  intro b hb
  by_cases hqt : q t = 1
  · simp [hqt]
  have hcard : Nat.card (Subgroup.zpowers (q t)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa using congrArg q ht.sq_eq_one) hqt
  have hmap : (Subgroup.zpowers (q t)).map (MulAut.conj b).toMonoidHom =
      Subgroup.zpowers (q t) := by
    rw [← MonoidHom.map_zpowers]
    apply weakly_closed_map_of_surjective S (Subgroup.zpowers t) hJS hJweak q hq b
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hb
  have hmem : b * q t * b⁻¹ ∈ Subgroup.zpowers (q t) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom (Subgroup.mem_zpowers _)
  let x : Subgroup.zpowers (q t) := ⟨b * q t * b⁻¹, hmem⟩
  let y : Subgroup.zpowers (q t) := ⟨q t, Subgroup.mem_zpowers _⟩
  have hx : x ≠ 1 := by
    intro h
    apply hqt
    have hv := congrArg Subtype.val h
    have hi := congrArg (fun a : H => b⁻¹ * a * b) hv
    simpa [x, mul_assoc] using hi
  have hy : y ≠ 1 := fun h => hqt (congrArg Subtype.val h)
  exact congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : Subgroup.zpowers (q t))).mp
    hcard).unique hx hy)

end Glauberman.ZStar

