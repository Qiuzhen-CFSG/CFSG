module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts


/-!
# Compatibility of prime-order symplectic transvection lifts

If the central kernel has order prime to p, two additive lifts of the same
transvection group differ pointwise by a kernel element of order dividing p.
The cyclic-preimage calculation makes their quotient a p-element, so the
lifts agree. Conjugating and rescaling then prove the corresponding identities
for any family of additive lifts. Orthogonal directions commute upstairs.
The final theorem applies this to the existing generating family, with the
literal `Matrix.PSp4Three.parameterHom` as its projection.

The defining-prime exclusion is an explicit premise here. These identities
alone are not asserted to present Sp₄, and this module does not construct a
global section. They support the local calculations in the central-closure
argument behind Aschbacher–Smith I.1.4, printed p.408, and GLS3 §6.1.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections
open Matrix.PSp4Three
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Group E]

private theorem parameter_pow (a : Multiplicative (ZMod p)) : a ^ p = 1 := by
  change Multiplicative.ofAdd (p • a.toAdd) = Multiplicative.ofAdd 0
  simp [nsmul_eq_mul]

/-- Additive lifts are unique when the central kernel has no p-torsion. -/
theorem transvection_lift_unique
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hp : ¬ p ∣ Nat.card f.toMonoidHom.ker)
    (v : Vector 2 (ZMod p)) (s t : Multiplicative (ZMod p) →* E)
    (hs : f.toMonoidHom.comp s = parameterHom v)
    (ht : f.toMonoidHom.comp t = parameterHom v) : s = t := by
  apply MonoidHom.ext
  intro a
  have hs' : f.toMonoidHom (s a) = parameterHom v a := DFunLike.congr_fun hs a
  have ht' : f.toMonoidHom (t a) = parameterHom v a := DFunLike.congr_fun ht a
  have hc : Commute (s a) (t a) :=
    transvection_preimage_commute f.toMonoidHom f.surjective f.ker_le_center v
      ⟨a, hs'.symm⟩ ⟨a, ht'.symm⟩
  let z : f.toMonoidHom.ker := ⟨s a * (t a)⁻¹, by
    change f.toMonoidHom (s a * (t a)⁻¹) = 1
    rw [map_mul, map_inv, hs', ht', mul_inv_cancel]⟩
  have hzpow : z ^ p = 1 := by
    apply Subtype.ext
    change (s a * (t a)⁻¹) ^ p = 1
    rw [hc.inv_right.mul_pow, inv_pow, ← map_pow, ← map_pow, parameter_pow,
      map_one, map_one, inv_one, mul_one]
  have hz : z = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp)
      (orderOf_dvd_of_pow_eq_one hzpow) (orderOf_dvd_natCard z))
  exact mul_inv_eq_one.mp (congrArg Subtype.val hz)

/-- Conjugation by the covering group agrees with the actual matrix action. -/
theorem transvection_lifts_conjugate
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hp : ¬ p ∣ Nat.card f.toMonoidHom.ker)
    (s : Vector 2 (ZMod p) → Multiplicative (ZMod p) →* E)
    (hs : ∀ v, f.toMonoidHom.comp (s v) = parameterHom v)
    (g : E) (v : Vector 2 (ZMod p)) (a : Multiplicative (ZMod p)) :
    g * s v a * g⁻¹ = s (f.toMonoidHom g • v) a := by
  have he : (MulAut.conj g).toMonoidHom.comp (s v) = s (f.toMonoidHom g • v) := by
    apply transvection_lift_unique f hp (f.toMonoidHom g • v)
    · apply MonoidHom.ext
      intro b
      change f.toMonoidHom (g * s v b * g⁻¹) = transvection _ b.toAdd
      have hsb : f.toMonoidHom (s v b) = transvection v b.toAdd :=
        DFunLike.congr_fun (hs v) b
      rw [map_mul, map_mul, map_inv, hsb]
      exact transvection_conjugate _ _ _
    · exact hs _
  exact DFunLike.congr_fun he a

/-- Orthogonal matrix directions have commuting additive lifts. -/
theorem transvection_lifts_commute
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hp : ¬ p ∣ Nat.card f.toMonoidHom.ker)
    (s : Vector 2 (ZMod p) → Multiplicative (ZMod p) →* E)
    (hs : ∀ v, f.toMonoidHom.comp (s v) = parameterHom v)
    (v w : Vector 2 (ZMod p)) (hvw : form v w = 0)
    (a b : Multiplicative (ZMod p)) : Commute (s v a) (s w b) := by
  have h := transvection_lifts_conjugate f hp s hs (s v a) w b
  have hsva : f.toMonoidHom (s v a) = transvection v a.toAdd :=
    DFunLike.congr_fun (hs v) a
  have hfix : f.toMonoidHom (s v a) • w = w := by
    rw [hsva, transvection_apply, form_swap w v, hvw]
    simp
  rw [hfix] at h
  exact (mul_inv_eq_iff_eq_mul.mp h)

private def scaleParameter (c : ZMod p) : Multiplicative (ZMod p) →* Multiplicative (ZMod p) :=
  (AddMonoidHom.mulLeft c).toMultiplicative

/-- Scaling a direction rescales its lifted parameter by the square. -/
theorem transvection_lifts_scale
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hp : ¬ p ∣ Nat.card f.toMonoidHom.ker)
    (s : Vector 2 (ZMod p) → Multiplicative (ZMod p) →* E)
    (hs : ∀ v, f.toMonoidHom.comp (s v) = parameterHom v)
    (v : Vector 2 (ZMod p)) (c a : ZMod p) :
    s (c • v) (.ofAdd a) = s v (.ofAdd (c ^ 2 * a)) := by
  have he : s (c • v) = (s v).comp (scaleParameter (c ^ 2)) := by
    apply transvection_lift_unique f hp (c • v)
    · exact hs _
    · apply MonoidHom.ext
      intro b
      change f.toMonoidHom (s v (.ofAdd (c ^ 2 * b.toAdd))) = transvection (c • v) b.toAdd
      have hsb : f.toMonoidHom (s v (.ofAdd (c ^ 2 * b.toAdd))) =
          transvection v (c ^ 2 * b.toAdd) :=
        DFunLike.congr_fun (hs v) (.ofAdd (c ^ 2 * b.toAdd))
      rw [hsb]
      exact (transvection_scale _ _ _).symm
  exact DFunLike.congr_fun he (.ofAdd a)

/-- Apply uniqueness to the literal additive sections and generation theorem. -/
theorem exists_generating_equivariant_transvection_lifts (hp : 3 < p)
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hk : ¬ p ∣ Nat.card f.toMonoidHom.ker) :
    ∃ s : Vector 2 (ZMod p) → Multiplicative (ZMod p) →* E,
      (∀ v, f.toMonoidHom.comp (s v) = parameterHom v) ∧
      Subgroup.closure (Set.range (fun a : Vector 2 (ZMod p) × Multiplicative (ZMod p) =>
        s a.1 a.2)) = ⊤ ∧
      (∀ (g : E) (v : Vector 2 (ZMod p)) (a : Multiplicative (ZMod p)),
        g * s v a * g⁻¹ = s (f.toMonoidHom g • v) a) ∧
      (∀ (v : Vector 2 (ZMod p)) (c a : ZMod p),
        s (c • v) (.ofAdd a) = s v (.ofAdd (c ^ 2 * a))) ∧
      (∀ (v w : Vector 2 (ZMod p)), form v w = 0 →
        ∀ (a b : Multiplicative (ZMod p)), Commute (s v a) (s w b)) := by
  obtain ⟨s, hs, hgen⟩ := exists_generating_transvection_lifts hp f
  exact ⟨s, hs, hgen, transvection_lifts_conjugate f hk s hs,
    transvection_lifts_scale f hk s hs, transvection_lifts_commute f hk s hs⟩

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections
