module
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.FixedWords
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel

/-!
# Counting the torus through the actual elementary central quotient

The expanded fixed tuples already have explicit elementary lifts, built from
folded root words. If the four split coroot coordinates are faithful and have
image the original split torus, those lifts give an equivalence from one
extension-field unit and one fixed-field unit onto the descended torus. The
proved injectivity of the actual central quotient supplies injectivity here.
Multiplicativity of the split parametrization upgrades this to a group
isomorphism. Thus the descended torus has order (q³ - 1)(q - 1), an odd number
in characteristic two. The split matrix inputs remain explicit hypotheses.

Source: GLS3 2.3.4(c), 2.3.8(a), and §2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat.TorusCoordinates
open Parabolics

/-- The descended matrix word attached to an orbit tuple. -/
def orbitToTorus (P : Parameters) (hp : P.prime = 2) (a : OrbitParameters P) : torus P :=
  ⟨toCarrier P (orbitElementary P hp a),
    ⟨orbitElementary P hp a, by
      change elementaryInclusion P (orbitElementary P hp a) ∈ splitTorus P
      rw [inclusion_orbitElementary]
      exact product_mem P _, rfl⟩⟩

private theorem orbitToTorus_injective (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P)) : Function.Injective (orbitToTorus P hp) := by
  intro a b hab
  apply (fixedCoordinatesEquiv P).injective
  apply Subtype.ext
  apply hinj
  have he := ElementaryCentralKernel.toCarrier_injective P hp (congrArg Subtype.val hab)
  exact (inclusion_orbitElementary P hp a).symm.trans
    ((congrArg (elementaryInclusion P) he).trans (inclusion_orbitElementary P hp b))

private theorem orbitToTorus_surjective (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P))
    (hrange : Set.range (product P) = (splitTorus P : Set (SplitGroup P))) :
    Function.Surjective (orbitToTorus P hp) := by
  intro g
  obtain ⟨x, hx, hxg⟩ := g.property
  have hx' : elementaryInclusion P x ∈ Set.range (product P) :=
    (Set.ext_iff.mp hrange (elementaryInclusion P x)).mpr hx
  obtain ⟨a, ha⟩ := hx'
  have hfix : twist P a = a := (product_fixed_iff P hp hinj a).mp (by
    rw [ha]
    exact x.val.property)
  let b := (fixedCoordinatesEquiv P).symm ⟨a, hfix⟩
  have hb : expand P b = a := congrArg Subtype.val
    ((fixedCoordinatesEquiv P).apply_symm_apply ⟨a, hfix⟩)
  have he : orbitElementary P hp b = x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (inclusion_orbitElementary P hp b).trans ((congrArg (product P) hb).trans ha)
  exact ⟨b, Subtype.ext ((congrArg (toCarrier P) he).trans hxg)⟩

/-- Fixed parameters give the actual descended torus once the split normal form is proved. -/
def torusEquivOfCoordinates (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P))
    (hrange : Set.range (product P) = (splitTorus P : Set (SplitGroup P))) :
    OrbitParameters P ≃ torus P := by
  exact Equiv.ofBijective (orbitToTorus P hp)
    (by exact ⟨orbitToTorus_injective P hp hinj, orbitToTorus_surjective P hp hinj hrange⟩)

@[simp] theorem torusEquivOfCoordinates_val (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P))
    (hrange : Set.range (product P) = (splitTorus P : Set (SplitGroup P)))
    (a : OrbitParameters P) :
    (torusEquivOfCoordinates P hp hinj hrange a).val = toCarrier P (orbitElementary P hp a) := rfl

def torusMulEquivOfCoordinates (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P))
    (hrange : Set.range (product P) = (splitTorus P : Set (SplitGroup P)))
    (hmul : ∀ a b, product P (a * b) = product P a * product P b) :
    OrbitParameters P ≃* torus P where
  toEquiv := torusEquivOfCoordinates P hp hinj hrange
  map_mul' a b := by
    apply Subtype.ext
    change toCarrier P (orbitElementary P hp (a * b)) =
      toCarrier P (orbitElementary P hp a) * toCarrier P (orbitElementary P hp b)
    have he : orbitElementary P hp (a * b) =
        orbitElementary P hp a * orbitElementary P hp b := by
      apply Subtype.ext
      apply Subtype.ext
      change elementaryInclusion P (orbitElementary P hp (a * b)) =
        elementaryInclusion P (orbitElementary P hp a * orbitElementary P hp b)
      calc
        _ = product P (expand P (a * b)) := inclusion_orbitElementary P hp _
        _ = product P (expand P a * expand P b) := congrArg (product P) (expand_mul P a b)
        _ = product P (expand P a) * product P (expand P b) := hmul _ _
        _ = elementaryInclusion P (orbitElementary P hp a) *
            elementaryInclusion P (orbitElementary P hp b) :=
          congrArg₂ (· * ·) (inclusion_orbitElementary P hp a).symm
            (inclusion_orbitElementary P hp b).symm
        _ = _ := (map_mul _ _ _).symm
    exact (congrArg (toCarrier P) he).trans (map_mul _ _ _)

theorem card_torus_of_coordinates (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P))
    (hrange : Set.range (product P) = (splitTorus P : Set (SplitGroup P))) :
    Nat.card (torus P) = (P.q ^ 3 - 1) * (P.q - 1) := by
  rw [← Nat.card_congr (torusEquivOfCoordinates P hp hinj hrange),
    Nat.card_prod, Nat.card_units, Nat.card_units, card_extensionField, card_fixedField]

theorem odd_torus_order (P : Parameters) (hp : P.prime = 2) :
    Odd ((P.q ^ 3 - 1) * (P.q - 1)) := by
  have hq : Even P.q := by
    rw [Parameters.q, hp]
    exact (show Even (2 : ℕ) by decide).pow_of_ne_zero (Nat.ne_of_gt P.exponent_pos)
  have hq3 : Even (P.q ^ 3) := hq.pow_of_ne_zero (by decide)
  have hq1 : 1 ≤ P.q := le_trans (by decide) P.q_ge_two
  have hq31 : 1 ≤ P.q ^ 3 := one_le_pow₀ hq1
  have h1 : Odd (P.q - 1) := (Nat.odd_sub' hq1).mpr (by simpa)
  have h3 : Odd (P.q ^ 3 - 1) := (Nat.odd_sub' hq31).mpr (by simpa)
  exact h3.mul h1

end Triality.Standard.ConcreteBruhat.TorusCoordinates
