module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.Quotient
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.Coordinates
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.CorootWords
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.QuotientTorus
public import Theory.GroupTheory.PrimeRankWitness
import Mathlib.Tactic

/-!
# Twisted E6 root-normalizer obstruction: assembly

An injective three-coordinate fixed-field torus in the genuine projective
root normalizer supplies an elementary odd-prime subgroup of rank three.
The literal fixed root curve makes this normalizer two-local when it
survives the center quotient faithfully. The two-local definition of
quasithinness then gives a contradiction.

The folded coroot words construct this torus inside the subgroup generated
by two-elements of the pinned graph–field fixed group. Conjugation by the
fourth coroot proves root survival; the first three folded root characters
prove torus faithfulness after the literal center quotient. Assembling
these constructions excludes every `Model 2 m` with `0 < m`, without any
additional geometric or model-comparison premise.

Source: the torus obstruction in Aschbacher–Smith A.2.18, printed p.40,
used for Theorem D/14.8.2(1), printed pp.1078–1079. The underlying pinned
carrier and quotient convention are those of GLS3 §§2.2–2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace TwistedE6.TheoremDRootNormalizer
noncomputable section

/-- Rank-three odd torsion in the actual root normalizer contradicts quasithinness.
The unconditional application below supplies both geometric premises. -/
theorem not_quasithin_of_normalizer_torus (m : ℕ) (hm : 0 < m)
    (hroot : Function.Injective (projectiveRootHom m true 3))
    (f : (Fin 3 → (FixedField m)ˣ) →* rootNormalizer m) (hf : Function.Injective f) :
    ¬ IsQuasithin (Model 2 m) := by
  intro hG
  obtain ⟨p, hp, ho, hc⟩ := exists_fixed_prime m hm
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let c : (Fin 3 → rootsOfUnity p (FixedField m)) →* (Fin 3 → (FixedField m)ˣ) :=
    { toFun a i := (a i).val
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hpow (u : rootsOfUnity p (FixedField m)) : u ^ p = 1 :=
    Subtype.ext ((mem_rootsOfUnity p u.val).mp u.property)
  have hr : 3 ≤ primeRank p (rootNormalizer m) := by
    apply primeRank_ge_of_elementary_embedding
      (A := Fin 3 → rootsOfUnity p (FixedField m))
      (fun a => funext (fun i => hpow (a i)))
      (by rw [Nat.card_fun, hc, Nat.card_fin]) (f.comp c)
    apply hf.comp
    intro a b he
    funext i
    exact Subtype.ext (congrFun he i)
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG _
    (rootNormalizer_isTwoLocal m hroot) p hp ho
  omega

/-- The full fixed root curve at node 3 embeds in the genuine central quotient. -/
theorem projectiveRootHom_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (projectiveRootHom m true 3) :=
  projectiveRootHom_injective_of_torus_lift m (foldedTorus m) (foldedTorus_ambient m) hm

/-- The first three folded coroots in the normalizer of the full fixed root curve. -/
def normalizerTorus (m : ℕ) : (Fin 3 → (FixedField m)ˣ) →* rootNormalizer m :=
  liftedTorusNormalizer m (foldedTorus m) (foldedTorus_ambient m)

/-- This torus uses the literal defining-characteristic words and central quotient. -/
@[simp] theorem normalizerTorus_val (m : ℕ) (a : Fin 3 → (FixedField m)ˣ) :
    (normalizerTorus m a).val = toModel 2 m (foldedTorus m (threeCoordinates m a)) := rfl

theorem normalizerTorus_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (normalizerTorus m) :=
  liftedTorusNormalizer_injective m (foldedTorus m) (foldedTorus_ambient m) hm

/-- Twisted E6 over `q = 2^(m+1) > 2` is not quasithin: its genuine root
two-local normalizer contains an elementary odd-prime subgroup of rank three. -/
theorem not_quasithin (m : ℕ) (hm : 0 < m) : ¬ IsQuasithin (Model 2 m) :=
  not_quasithin_of_normalizer_torus m hm (projectiveRootHom_injective m hm)
    (normalizerTorus m) (normalizerTorus_injective m hm)

end
end TwistedE6.TheoremDRootNormalizer
