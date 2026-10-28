module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ElementaryImage.Multiplication
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.ElementaryAbelian.Basic

/-!
# An elementary subgroup of order q⁵ in genuine binary triality

The last three folded positive roots, 2a+b, 3a+b and 3a+2b, give one
cubic-field parameter and two fixed-field parameters. In the published
central-radical normal form these are precisely the tuples with their first
two cubic coordinates zero. The collected multiplication restricts to
addition. Injectivity of the concrete coordinates, including the actual
central quotient, therefore embeds their additive group in the carrier.

For q = 2^n this proves the lower bound 5*n, including n = 1. The upper
bound requires a separate argument for arbitrary elementary subgroups.

Sources: GLS3 §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`), and the
triality two-rank used in Aschbacher–Smith G.9, printed p.356
(`refs/quasithin.pdf`).
-/

@[expose] public section

open Triality.Standard
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.CentralRootSquare
open Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
namespace Triality.Standard.TwoRank
noncomputable section

/-- Parameters of the three highest folded root groups. -/
abbrev TailParameters (P : Parameters) := ExtensionField P × (Fin 2 → fixedField P)
/-- Inclusion into the published central-radical coordinates. -/
def tailParameters (P : Parameters) (v : TailParameters P) : RootOrbitParameters P .central :=
  (![0, 0, v.1], v.2)

theorem tailParameters_add (P : Parameters) (v w : TailParameters P) :
    tailParameters P (v + w) = multiply P (tailParameters P v) (tailParameters P w) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [tailParameters, multiply, higherCoefficient, -fieldFrobenius_apply]
  · funext i
    fin_cases i <;> simp [tailParameters, multiply, higherCoefficient, -fieldFrobenius_apply]

/-- The additive tail, embedded in the actual central radical. -/
def tailRadicalHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (TailParameters P) →* radical P .central where
  toFun v := coordinates P hp (tailParameters P v.toAdd)
  map_one' := by
    apply Subtype.ext
    rw [coordinates_val, rootElement_factorization]
    simp [tailParameters, extendOrbit]
  map_mul' v w := by
    change coordinates P hp (tailParameters P (v.toAdd + w.toAdd)) = _
    rw [tailParameters_add, coordinates_multiply]

theorem tailRadicalHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (tailRadicalHom P hp) := by
  intro v w h
  have he := (coordinates P hp).injective h
  change v.toAdd = w.toAdd
  apply Prod.ext
  · exact congrArg (fun x : RootOrbitParameters P .central => x.1 2) he
  · exact congrArg (fun x : RootOrbitParameters P .central => x.2) he

/-- The same faithful tail embedding into the genuine carrier. -/
def tailHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (TailParameters P) →* Carrier P :=
  (radical P .central).subtype.comp (tailRadicalHom P hp)

theorem tailHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (tailHom P hp) :=
  Subtype.val_injective.comp (tailRadicalHom_injective P hp)

theorem card_tailParameters (P : Parameters) : Nat.card (TailParameters P) = P.q ^ 5 := by
  simp only [TailParameters, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    card_extensionField, card_fixedField, ← pow_add]

/-- Each tail element has order dividing two, also over the smallest field. -/
theorem tail_pow_two (P : Parameters) (hp : P.prime = 2)
    (a : Multiplicative (TailParameters P)) : a ^ 2 = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  change 2 • a.toAdd = 0
  rw [two_nsmul]
  apply Prod.ext
  · exact CharTwo.add_self_eq_zero _
  · funext i
    exact CharTwo.add_self_eq_zero _

/-- The required elementary subgroup is an actual homomorphism range. -/
def tailSubgroup (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (tailHom P hp).range

theorem tailSubgroup_elementary (P : Parameters) (hp : P.prime = 2) :
    IsElementaryAbelian 2 (tailSubgroup P hp) := by
  refine { toIsMulCommutative := inferInstanceAs (IsMulCommutative (tailHom P hp).range)
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  obtain ⟨a, ha⟩ := x.property
  change x.val ^ 2 = 1
  rw [← ha, ← map_pow, tail_pow_two P hp, map_one]

theorem card_tailSubgroup (P : Parameters) (hp : P.prime = 2) :
    Nat.card (tailSubgroup P hp) = P.q ^ 5 := by
  change Nat.card (tailHom P hp).range = P.q ^ 5
  rw [← Nat.card_congr (MonoidHom.ofInjective (tailHom_injective P hp)).toEquiv]
  exact card_tailParameters P

/-- The lower half of the exact triality rank calculation, including n = 1. -/
theorem twoRank_ge_five_mul (n : ℕ) (hn : 0 < n) :
    5 * n ≤ primeRank 2 (BinaryCarrier n hn) := by
  apply primeRank_ge_of_elementary_embedding (f := tailHom (binaryParameters n hn) rfl)
  · exact tail_pow_two _ rfl
  · change Nat.card (TailParameters (binaryParameters n hn)) = 2 ^ (5 * n)
    rw [card_tailParameters, binaryParameters_q, ← pow_mul, Nat.mul_comm]
  · exact tailHom_injective _ rfl
end
end Triality.Standard.TwoRank
