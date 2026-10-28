module

public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Automorphism ranks from irreducibility in characteristic two

An involution centralizing an irreducibly acting subgroup has square-zero
intertwining displacement. Schur's lemma kills that displacement. Thus every
elementary two-subgroup normalizing the actor embeds in its automorphism
group, and the ambient two-rank is bounded by that automorphism two-rank.

This extends the binary argument to every characteristic-two coefficient
field without assuming irreducibility after restricting scalars. It is the
rank input for the triality fixed-space estimate in Guralnick--Malle,
*Classification of 2F-modules, II*, Lemma 8.6 (internal pp.56--57).
-/

public section

namespace Representation.CharacteristicTwoIrreducible

variable {E G V : Type*} [Field E] [CharP E 2] [Group G]
  [AddCommGroup V] [Module E V]
  (ρ : Representation E G V) (L : Subgroup G)
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
      have he := @two_smul E V _ _ _ w
      have hz : (2 : E) = 0 := CharP.cast_eq_zero E 2
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

/-- Conjugation on a normally and irreducibly acting subgroup bounds ambient
two-rank, even when conjugation on the entire ambient group has a kernel. -/
theorem primeRank_le_automorphisms {E G V : Type*} [Field E] [CharP E 2] [Group G] [Finite G]
    [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (L : Subgroup G) [L.Normal]
    [Representation.IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ) :
    primeRank 2 G ≤ primeRank 2 (MulAut L) := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  have hn : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  let f := L.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hf' : Function.Injective f := elementary_conjugation_injective ρ L hf A hn
  have himage : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut L)).mp le_rfl f.range himage
  exact (Nat.card_congr (MonoidHom.ofInjective hf').toEquiv).le.trans hc

end Representation.CharacteristicTwoIrreducible

namespace Representation

/-- The displacement of any subgroup element is bounded by the codimension
of that subgroup's fixed space, over the original coefficient field. -/
theorem displacement_finrank_le_fixedSpace_codim
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (ρ : Representation E G V)
    (A : Subgroup G) {t : G} (ht : t ∈ A) :
    Module.finrank E (LinearMap.range (ρ t - LinearMap.id)) ≤
      Module.finrank E (V ⧸ invariants (ρ.comp A.subtype)) := by
  have hle : invariants (ρ.comp A.subtype) ≤ (ρ t - LinearMap.id).ker := by
    intro v hv
    change ρ t v - v = 0
    exact sub_eq_zero.mpr (hv ⟨t, ht⟩)
  have hr := (ρ t - LinearMap.id).finrank_range_add_finrank_ker
  have hq := (invariants (ρ.comp A.subtype)).finrank_quotient_add_finrank
  have hf := Submodule.finrank_mono hle
  omega

end Representation
