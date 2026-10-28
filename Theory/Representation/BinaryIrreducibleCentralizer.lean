module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Elementary abelian actors on an irreducibly acting subgroup

In a faithful binary representation, no nonidentity involution centralizes
an irreducibly acting subgroup. Indeed its displacement is an intertwining
endomorphism whose square is zero. Schur's lemma makes that endomorphism
zero. Consequently, an elementary abelian two-subgroup normalizing the
irreducibly acting subgroup embeds into its automorphism group by actual
conjugation. No finiteness or classification hypothesis is needed.

This is the automorphism-rank reduction used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript of
1 March 2004, G.9.3, printed p.356.
-/

public section

namespace Representation.BinaryIrreducibleCentralizer

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)]

/-- A centralizing element whose square is one is trivial. -/
theorem centralizing_square_one_eq_one (hf : Function.Injective ρ)
    {x : G} (hx : x ^ 2 = 1) (hc : x ∈ Subgroup.centralizer (L : Set G)) : x = 1 := by
  let σ := ρ.comp L.subtype
  let f : IntertwiningMap σ σ := {
    toLinearMap := ρ x - 1
    isIntertwining' := by
      intro g
      ext v
      change ρ x (ρ g v) - ρ g v = ρ g (ρ x v - v)
      rw [map_sub]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hc) g g.property
      have he := congrArg (fun y : G => ρ y v) hcomm
      exact congrArg (fun w : V => w - ρ g v)
        (by simpa only [map_mul, Module.End.mul_apply] using he.symm) }
  have htwice (v : V) : ρ x (ρ x v) = v := by
    have he := congrArg (fun y : G => ρ y v) hx
    simpa only [map_pow, pow_two, map_mul, Module.End.mul_apply, map_one,
      Module.End.one_apply] using he
  have hzero (v : V) : f (f v) = 0 := by
    change ρ x (ρ x v - v) - (ρ x v - v) = 0
    rw [map_sub, htwice]
    have htwo (w : V) : w + w = 0 := by
      have he := @two_smul (ZMod 2) V _ _ _ w
      have hz : (2 : ZMod 2) = 0 := by decide
      rw [hz, zero_smul] at he
      exact he.symm
    have hn (w : V) : -w = w := neg_eq_iff_add_eq_zero.mpr (htwo w)
    simp only [sub_eq_add_neg, hn]
    rw [add_assoc, ← add_assoc (ρ x v), htwo, zero_add, htwo]
  have hfzero : f = 0 := by
    rcases IsIrreducible.injective_or_eq_zero f with hi | hz
    · ext v
      apply hi
      simpa using hzero v
    · exact hz
  apply hf
  ext v
  have he := congrArg (fun g : IntertwiningMap σ σ => g v) hfzero
  exact (sub_eq_zero.mp he).trans (by simp)

/-- Conjugation embeds a normalizing elementary abelian two-subgroup into
the automorphism group of an irreducibly acting subgroup. -/
theorem elementary_conjugation_injective (hf : Function.Injective ρ)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    Function.Injective (L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)) := by
  apply (L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro a ha
  apply Subtype.ext
  apply centralizing_square_one_eq_one ρ L hf
  · exact elemPow_eq_one_of_isElementaryAbelian (a : G) a.property
  · change Subgroup.inclusion hAL a ∈ L.normalizerMonoidHom.ker at ha
    rw [Subgroup.normalizerMonoidHom_ker] at ha
    exact ha

end Representation.BinaryIrreducibleCentralizer
