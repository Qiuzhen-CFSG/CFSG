module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.BorelReduction
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.Triality.ParabolicGeometry

/-!
# Concrete Borel geometry for the triality Cartan action

The torus of `CartanAction` is the same coroot-word subgroup as the concrete
Bruhat torus. Its fixed coordinates are an extension-field unit a and a
q-Frobenius-fixed unit b, with word h₀(a) h₂(a^q) h₃(a^(q²)) h₁(b).
The upstream folded rank-one construction places this word in the elementary
fixed group, and its faithful central quotient gives the displayed torus
isomorphism and order (q³ - 1)(q - 1).

The concrete positive-times-torus factorization, trivial intersection, and
relative normality supply three fields of `BorelGeometry`. The proved Bruhat
normalizer equality supplies its fourth field. The positive subgroup is also
the underlying subgroup of the existing concrete Sylow two-subgroup. These
results hold for every positive binary exponent, hence in particular n > 1.

This discharges the geometric input of the triality action argument; matching
an arbitrary source Cartan and supplying automorphism coverage remain the
separate source-assembly tasks.

Sources: GLS3 §§2.3–2.6, `refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith,
`refs/quasithin.pdf`, A.3.15(5), printed pp.50–51, and the proof of
Proposition 1.3.4, p.511.
-/

public section
noncomputable section
namespace Triality.Standard.CartanAction
open Parabolics
open ConcreteBruhat.TorusCoordinates

/-- Both APIs use the closure of the same original simple-coroot words. -/
theorem splitTorus_eq_concreteBruhat (P : Parameters) :
    splitTorus P = ConcreteBruhat.splitTorus P := rfl

/-- Both APIs use the same elementary restriction and central-quotient map. -/
theorem torus_eq_concreteBruhat (P : Parameters) :
    torus P = ConcreteBruhat.torus P := rfl

/-- The actual finite Cartan torus, with its extension-field and fixed-field units. -/
def torusCoordinates (P : Parameters) (hp : P.prime = 2) :
    (ExtensionField P)ˣ × (fixedField P)ˣ ≃* torus P :=
  ConcreteBruhat.TorusCoordinates.torusMulEquiv P hp

@[simp] theorem torusCoordinates_val (P : Parameters) (hp : P.prime = 2)
    (a : (ExtensionField P)ˣ) (b : (fixedField P)ˣ) :
    (torusCoordinates P hp (a, b)).val = toCarrier P (orbitElementary P hp (a, b)) :=
  ConcreteBruhat.TorusCoordinates.torusMulEquiv_val P hp (a, b)

private theorem frobenius_eq_pow (P : Parameters) (a : (ExtensionField P)ˣ) :
    frobenius P a = a ^ P.q := by
  apply Units.ext
  exact fieldFrobenius_apply P a.val

/-- The diagram orientation is 0 → 2 → 3 → 0, with the central node 1 fixed.
The word is the inclusion of an explicit elementary element before quotienting. -/
theorem torusCoordinates_word (P : Parameters) (hp : P.prime = 2)
    (a : (ExtensionField P)ˣ) (b : (fixedField P)ˣ) :
    elementaryInclusion P (orbitElementary P hp (a, b)) =
      torusWord P 0 a * torusWord P 2 (a ^ P.q) *
        torusWord P 3 (a ^ (P.q ^ 2)) * torusWord P 1 (fixedUnit P b) := by
  rw [inclusion_orbitElementary]
  change torusWord P 0 a * torusWord P 2 (frobenius P a) *
    torusWord P 3 (frobenius P (frobenius P a)) * torusWord P 1 (fixedUnit P b) = _
  simp only [frobenius_eq_pow, ← pow_mul, ← pow_two]

theorem fixedUnit_pow_q (P : Parameters) (b : (fixedField P)ˣ) :
    (fixedUnit P b) ^ P.q = fixedUnit P b := by
  rw [← frobenius_eq_pow, frobenius_fixedUnit]

theorem card_torus (P : Parameters) (hp : P.prime = 2) :
    Nat.card (torus P) = (P.q ^ 3 - 1) * (P.q - 1) :=
  ConcreteBruhat.TorusCoordinates.card_torus P hp

/-- All four geometric premises are proved for the original triality carrier. -/
theorem borelGeometry (P : Parameters) (hp : P.prime = 2) : BorelGeometry P where
  disjoint := ConcreteBruhat.disjoint_unipotent_torus P hp
  normalizes := (torus_le_borel P).trans (ConcreteBruhat.borel_le_normalizer_unipotent P hp)
  product := by
    intro d hd
    obtain ⟨u, hu, t, ht, he⟩ := (ConcreteBruhat.borel_eq_mul P hp).le hd
    exact ⟨u, hu, t, ht, he.symm⟩
  normalizer_eq := ConcreteBruhat.normalizer_unipotent_eq_borel P hp

theorem borelGeometry_binary (n : ℕ) (hn : 0 < n) :
    BorelGeometry (binaryParameters n hn) := borelGeometry _ rfl

/-- The supplied Sylow subgroup is exactly the positive image used by the geometry. -/
theorem exists_unipotentSylow (P : Parameters) (hp : P.prime = 2) :
    ∃ S : Sylow 2 (Carrier P), (S : Subgroup (Carrier P)) = unipotent P :=
  ⟨unipotentSylow P hp, coe_unipotentSylow P hp⟩

end Triality.Standard.CartanAction
