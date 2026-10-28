module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ElementaryImage.Multiplication

/-!
# Elementary normal images in the central triality root layer

The full collected multiplication law makes the first two cubic coordinates
additive. A commutator has zero first layer and has third coordinate given by
the alternating sum of the two folded exchange coefficients. Commuting once
more leaves precisely two trace pairings in the singleton root groups; all
arbitrary higher input coordinates disappear.

For a normal subgroup of exponent two, its elements commute with these
internal commutators. Scalar closure of its first-layer image then allows the
cubic-field obstruction to force both first coordinates to vanish. Normality
is inside the radical, and every argument includes q = 2.

These are the additivity and elementary-image premises of
`le_radical_of_firstLayer_calculations`; the full parabolic action and final
rigidity assembly belong to its consumer.

Source: GLS3 2.4.5(b)(4) and §2.6 (`refs/KGroup/GLS3/chapter2.tex`), for the
central radical in Aschbacher–Smith F.1.12(I)(4), printed pp.263–264
(`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open scoped commutatorElement
namespace Triality.Standard.Parabolics.CentralRootSquare
open ElementaryImage

/-- The genuine first two cubic root coordinates form an additive quotient layer. -/
theorem firstLayer_mul (P : Parameters) (hp : P.prime = 2)
    (r s : radical P .central) :
    firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s := by
  obtain ⟨v, rfl⟩ := (coordinates P hp).surjective r
  obtain ⟨w, rfl⟩ := (coordinates P hp).surjective s
  rw [← coordinates_multiply, firstLayer_coordinates, firstLayer_coordinates,
    firstLayer_coordinates]
  rfl

namespace ElementaryImage

/-- The parameter in the third short-root orbit, positions (7,8,9). -/
def thirdLayer (P : Parameters) (hp : P.prime = 2)
    (r : radical P .central) : ExtensionField P :=
  ((coordinates P hp).symm r).1 2

@[simp] theorem thirdLayer_coordinates (P : Parameters) (hp : P.prime = 2)
    (v : RootOrbitParameters P .central) :
    thirdLayer P hp (coordinates P hp v) = v.1 2 := by
  simp [thirdLayer]

theorem thirdLayer_mul (P : Parameters) (hp : P.prime = 2)
    (r s : radical P .central) :
    thirdLayer P hp (r * s) = thirdLayer P hp r + thirdLayer P hp s +
      higherCoefficient P (firstLayer P hp s).1 (firstLayer P hp r).2 := by
  obtain ⟨v, rfl⟩ := (coordinates P hp).surjective r
  obtain ⟨w, rfl⟩ := (coordinates P hp).surjective s
  rw [← coordinates_multiply, thirdLayer_coordinates, thirdLayer_coordinates,
    thirdLayer_coordinates, firstLayer_coordinates, firstLayer_coordinates]
  rfl

private theorem firstLayer_inv (P : Parameters) (hp : P.prime = 2)
    (r : radical P .central) : firstLayer P hp r⁻¹ = -firstLayer P hp r := by
  apply eq_neg_of_add_eq_zero_left
  rw [← firstLayer_mul, inv_mul_cancel, firstLayer_one]

theorem firstLayer_commutator (P : Parameters) (hp : P.prime = 2)
    (r s : radical P .central) : firstLayer P hp ⁅r,s⁆ = 0 := by
  simp only [commutatorElement_def, firstLayer_mul, firstLayer_inv]
  abel

private theorem higher_zero_left (P : Parameters) (a : ExtensionField P) :
    higherCoefficient P 0 a = 0 := by simp [higherCoefficient, -fieldFrobenius_apply]

private theorem higher_zero_right (P : Parameters) (a : ExtensionField P) :
    higherCoefficient P a 0 = 0 := by simp [higherCoefficient, -fieldFrobenius_apply]

theorem thirdLayer_commutator (P : Parameters) (hp : P.prime = 2)
    (r s : radical P .central) :
    thirdLayer P hp ⁅r,s⁆ =
      higherCoefficient P (firstLayer P hp s).1 (firstLayer P hp r).2 +
      higherCoefficient P (firstLayer P hp r).1 (firstLayer P hp s).2 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hg : r * s = ⁅r,s⁆ * (s * r) := by
    simp only [commutatorElement_def]
    group
  have h := congrArg (thirdLayer P hp) hg
  simp only [thirdLayer_mul, firstLayer_commutator, firstLayer_mul,
    Prod.snd_zero, higher_zero_right, add_zero] at h
  have h' : higherCoefficient P (firstLayer P hp s).1 (firstLayer P hp r).2 =
      thirdLayer P hp ⁅r,s⁆ +
        higherCoefficient P (firstLayer P hp r).1 (firstLayer P hp s).2 := by
    apply add_left_cancel (a := thirdLayer P hp r + thirdLayer P hp s)
    convert h using 1
    abel
  rw [h', add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem multiply_commutator_left (P : Parameters) (hp : P.prime = 2)
    (v w : RootOrbitParameters P .central) (h0 : w.1 0 = 0) (h1 : w.1 1 = 0) :
    multiply P (0, ![armsPairing P (v.1 0) (w.1 2), armsPairing P (v.1 1) (w.1 2)])
      (multiply P w v) = multiply P v w := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [multiply, h0, h1, higher_zero_left, higher_zero_right, add_comm]
  · funext i
    fin_cases i <;>
      simp [multiply, h0, h1, higher_zero_left, higher_zero_right,
        -fieldFrobenius_apply]
    all_goals
      apply Subtype.ext
      simp only [Subfield.coe_add]
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero, add_comm]

/-- Commuting with a zero-first-layer element sees only its third parameter;
all arbitrary singleton parameters disappear. -/
theorem commutator_of_firstLayer_zero (P : Parameters) (hp : P.prime = 2)
    (r k : radical P .central) (hk : firstLayer P hp k = 0) :
    ⁅r,k⁆ = coordinates P hp
      (0, ![armsPairing P (firstLayer P hp r).1 (thirdLayer P hp k),
        armsPairing P (firstLayer P hp r).2 (thirdLayer P hp k)]) := by
  obtain ⟨v, rfl⟩ := (coordinates P hp).surjective r
  obtain ⟨w, rfl⟩ := (coordinates P hp).surjective k
  rw [firstLayer_coordinates] at hk
  have h0 : w.1 0 = 0 := congrArg Prod.fst hk
  have h1 : w.1 1 = 0 := congrArg Prod.snd hk
  have he : coordinates P hp v * coordinates P hp w =
      coordinates P hp (0, ![armsPairing P (v.1 0) (w.1 2),
        armsPairing P (v.1 1) (w.1 2)]) *
        (coordinates P hp w * coordinates P hp v) := by
    rw [← coordinates_multiply, ← coordinates_multiply, ← coordinates_multiply,
      multiply_commutator_left P hp v w h0 h1]
  rw [commutatorElement_def, he]
  group
  apply congrArg (coordinates P hp)
  simp [firstLayer, thirdLayer]

/-- The exact iterated commutator has only the two singleton root coordinates. -/
theorem iterated_commutator (P : Parameters) (hp : P.prime = 2)
    (r s t : radical P .central) :
    ⁅r,⁅s,t⁆⁆ = coordinates P hp
      (0, ![armsPairing P (firstLayer P hp r).1
          (higherCoefficient P (firstLayer P hp t).1 (firstLayer P hp s).2 +
            higherCoefficient P (firstLayer P hp s).1 (firstLayer P hp t).2),
        armsPairing P (firstLayer P hp r).2
          (higherCoefficient P (firstLayer P hp t).1 (firstLayer P hp s).2 +
            higherCoefficient P (firstLayer P hp s).1 (firstLayer P hp t).2)]) := by
  rw [commutator_of_firstLayer_zero P hp r ⁅s,t⁆ (firstLayer_commutator P hp s t),
    thirdLayer_commutator]


private theorem coordinates_zero (P : Parameters) (hp : P.prime = 2) :
    coordinates P hp (0, 0) = 1 := by
  apply Subtype.ext
  rw [coordinates_val, rootElement_factorization]
  simp [extendOrbit]

private theorem singleton_eq_zero_of_coordinates_eq_one
    (P : Parameters) (hp : P.prime = 2) (a b : fixedField P)
    (h : coordinates P hp (0, ![a,b]) = 1) : a = 0 ∧ b = 0 := by
  have he := (coordinates P hp).injective (h.trans (coordinates_zero P hp).symm)
  exact ⟨congrArg (fun v : RootOrbitParameters P .central => v.2 0) he,
    congrArg (fun v : RootOrbitParameters P .central => v.2 1) he⟩

private theorem elementary_commute {G : Type*} [Group G] (N : Subgroup G)
    (hsq : ∀ n ∈ N, (n : G) ^ 2 = 1) (r s : G) (hr : r ∈ N) (hs : s ∈ N) :
    Commute r s := by
  have hi (n : G) (hn : n ∈ N) : n⁻¹ = n := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hsq n hn
  show r * s = s * r
  rw [← hi (r*s) (N.mul_mem hr hs), mul_inv_rev, hi r hr, hi s hs]

private theorem commutator_mem_of_normal {G : Type*} [Group G]
    (N : Subgroup G) (hN : N.Normal) (s t : G) (hs : s ∈ N) : ⁅s,t⁆ ∈ N := by
  have hm := N.mul_mem hs (hN.conj_mem s⁻¹ (N.inv_mem hs) t)
  simpa only [commutatorElement_def, mul_assoc] using hm

private theorem normal_elementary_pairings (P : Parameters) (hp : P.prime = 2)
    (N : Subgroup (radical P .central)) (hN : N.Normal)
    (hsq : ∀ n ∈ N, (n : radical P .central) ^ 2 = 1)
    (r s t : radical P .central) (hr : r ∈ N) (hs : s ∈ N) :
    armsPairing P (firstLayer P hp r).1 (thirdLayer P hp ⁅s,t⁆) = 0 ∧
      armsPairing P (firstLayer P hp r).2 (thirdLayer P hp ⁅s,t⁆) = 0 := by
  have hc := elementary_commute N hsq r ⁅s,t⁆ hr (commutator_mem_of_normal N hN s t hs)
  apply singleton_eq_zero_of_coordinates_eq_one P hp
  rw [← commutator_of_firstLayer_zero P hp r ⁅s,t⁆ (firstLayer_commutator P hp s t)]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hc.eq

end ElementaryImage

/-- A normal exponent-two subgroup with scalar-closed first-layer image has
zero first layer. Normality is required only inside the radical. -/
theorem firstLayer_eq_zero_of_normal_elementary (P : Parameters) (hp : P.prime = 2)
    (N : Subgroup (radical P .central)) (hN : N.Normal)
    (hsq : ∀ n ∈ N, (n : radical P .central) ^ 2 = 1)
    (hscalar : ∀ c : ExtensionField P, ∀ r ∈ N, ∃ s ∈ N,
      firstLayer P hp s = c • firstLayer P hp r)
    (r : radical P .central) (hr : r ∈ N) : firstLayer P hp r = 0 := by
  apply Prod.ext
  · apply eq_zero_of_iterated_pairing P hp (firstLayer P hp r).1
    intro c d
    obtain ⟨s, hs, he⟩ := hscalar c r hr
    have h := (normal_elementary_pairings P hp N hN hsq r s
      (coordinates P hp (![0,d,0], 0)) hr hs).1
    rw [thirdLayer_commutator, firstLayer_coordinates, he] at h
    simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, higher_zero_left, zero_add] using h
  · apply eq_zero_of_iterated_pairing P hp (firstLayer P hp r).2
    intro c d
    obtain ⟨s, hs, he⟩ := hscalar c r hr
    have h := (normal_elementary_pairings P hp N hN hsq r s
      (coordinates P hp (![d,0,0], 0)) hr hs).2
    rw [thirdLayer_commutator, firstLayer_coordinates, he] at h
    have hsymmetric : higherCoefficient P d (c * (firstLayer P hp r).2) =
        higherCoefficient P (c * (firstLayer P hp r).2) d := by
      simp only [higherCoefficient]
      ring
    simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, higher_zero_right, add_zero,
      hsymmetric] using h

end Triality.Standard.Parabolics.CentralRootSquare
