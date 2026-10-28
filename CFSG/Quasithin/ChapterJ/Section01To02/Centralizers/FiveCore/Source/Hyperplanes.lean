module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.OddComplement
public import Theory.GroupAction.KleinFourFactorization.Ambient

/-!
# The hyperplane calculation for the odd complement

The z-class inverter normalizes the odd core. Its commuting action with z
gives the three fixed factors, with trivial common fixed subgroup because
i inverts C_P(z)=B₅. Conjugation by the supplied quaternion element identifies
the other two fixed subgroup orders. Brauer–Wielandt then gives
|P|=5|C_P(i)|², on the actual odd core and the literal ambient centralizers.

Construction of the local quaternion and inverter witnesses is still required;
this calculation does not assume that P is a five-group.

Source: Aschbacher–Smith, J.2.7(5), printed p.436 (PDF p.447).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
  (B5 : Sylow 5 d.toTypeRuSetup.H)

namespace FiveInverterData
variable (v : FiveInverterData c B5)

theorem normalizes_B5Image : v.i ∈ normalizer (B5Image B5 : Set G) := by
  have hf (x : G) (hx : x ∈ B5Image B5) : v.i*x*v.i⁻¹ ∈ B5Image B5 := by
    rw [v.inverts x hx]
    exact (B5Image B5).inv_mem hx
  intro x
  refine ⟨hf x, fun hx => ?_⟩
  have h := hf _ hx
  have hi : v.i * v.i = 1 := by simpa only [pow_two] using v.square
  have he : v.i * (v.i * x * v.i⁻¹) * v.i⁻¹ = x := by
    calc
      _ = (v.i*v.i) * x * (v.i*v.i)⁻¹ := by group
      _ = x := by rw [hi]; simp
  rwa [he] at h

theorem normalizes_fiveOddPart : v.i ∈ normalizer (fiveOddPart B5 : Set G) :=
  normalizer_B5Image_le_normalizer_fiveOddPart B5 (v.normalizes_B5Image c B5)

theorem commute_z : Commute c.z v.i := by
  have hi := v.mem_H
  rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff] at hi
  exact hi.symm

private def zActor : normalizer (fiveOddPart B5 : Set G) :=
  ⟨c.z, G5_normalizes_fiveOddPart B5 (c.z_mem_G5 B5)⟩

private def iActor : normalizer (fiveOddPart B5 : Set G) :=
  ⟨v.i, v.normalizes_fiveOddPart c B5⟩

private theorem zActor_square (hZ : Nat.card d.toTypeRuSetup.Z = 2) :
    (zActor c B5)^2 = 1 := Subtype.ext (c.z_involution_of_card hZ).2

private theorem iActor_square : (v.iActor c B5)^2 = 1 := Subtype.ext v.square

private theorem actors_commute : Commute (zActor c B5) (v.iActor c B5) :=
  Subtype.ext (v.commute_z c B5).eq

/-- The actual three-factor product, not merely generation by a subgroup join. -/
theorem factorization (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (q : FiveQuaternionData B5) (x : G) (hx : x ∈ fiveOddPart B5) :
    ∃ b ∈ B5Image B5,
      ∃ u ∈ fiveOddPart B5 ⊓ centralizer ({v.i} : Set G),
        ∃ w ∈ fiveOddPart B5 ⊓ centralizer ({c.z * v.i} : Set G),
          x = b*u*w := by
  have h := (fiveOddPart B5).exists_three_odd_centralizers (fiveOddPart_odd B5)
    (zActor c B5) (v.iActor c B5) (zActor_square c B5 hZ)
    (v.iActor_square c B5) (v.actors_commute c B5) x hx
  change ∃ b ∈ fiveOddPart B5 ⊓ centralizer ({c.z} : Set G),
    ∃ u ∈ fiveOddPart B5 ⊓ centralizer ({v.i} : Set G),
      ∃ w ∈ fiveOddPart B5 ⊓ centralizer ({c.z * v.i} : Set G), x = b*u*w at h
  rwa [c.fiveOddPart_inf_centralizer_z hZ B5 q] at h

/-- Inversion of the odd five-subgroup makes the common fixed group trivial. -/
theorem common_fixed_eq_bot (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (q : FiveQuaternionData B5) :
    (fiveOddPart B5 ⊓ centralizer ({c.z} : Set G)) ⊓ centralizer ({v.i} : Set G) = ⊥ := by
  rw [c.fiveOddPart_inf_centralizer_z hZ B5 q]
  apply eq_bot_iff.mpr
  intro x hx
  have hfix : v.i*x*v.i⁻¹ = x := by
    rw [← mem_centralizer_singleton_iff.mp hx.2, mul_inv_cancel_right]
  have he : x = x⁻¹ := hfix.symm.trans (v.inverts x hx.1)
  have h2 : x ^ 2 = 1 := by
    calc
      x ^ 2 = x*x := pow_two x
      _ = x⁻¹*x := congrArg (· * x) he
      _ = 1 := inv_mul_cancel x
  have h5 : x ^ 5 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx.1⟩ : B5Image B5))
    rw [B5Image_card hZ B5] at h
    exact congrArg Subtype.val h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp
    (show orderOf x ∣ 1 from Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one h5)))

/-- The supplied quaternion conjugator identifies the two other fixed orders. -/
theorem fixed_card_eq :
    Nat.card (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G) =
      Nat.card (fiveOddPart B5 ⊓ centralizer ({c.z*v.i} : Set G) : Subgroup G) := by
  obtain ⟨t, ht⟩ := v.fused
  have hnorm := G5_normalizes_fiveOddPart B5 t.property.2
  simpa only [ht] using (fiveOddPart B5).card_inf_centralizer_conj t hnorm v.i

/-- The source order formula applies to O(C_G(B₅)), before five-core recognition. -/
theorem oddPart_card_formula (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (q : FiveQuaternionData B5) :
    Nat.card (fiveOddPart B5) =
      5 * Nat.card (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G)^2 := by
  have h := (fiveOddPart B5).card_three_odd_centralizers (fiveOddPart_odd B5)
    (zActor c B5) (v.iActor c B5) (zActor_square c B5 hZ)
    (v.iActor_square c B5) (v.actors_commute c B5)
  change Nat.card (fiveOddPart B5) * Nat.card
      ((fiveOddPart B5 ⊓ centralizer ({c.z} : Set G)) ⊓ centralizer ({v.i} : Set G) : Subgroup G)^2 =
    Nat.card (fiveOddPart B5 ⊓ centralizer ({c.z} : Set G) : Subgroup G) *
    Nat.card (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G) *
    Nat.card (fiveOddPart B5 ⊓ centralizer ({c.z*v.i} : Set G) : Subgroup G) at h
  rw [v.common_fixed_eq_bot c B5 hZ q, card_bot, one_pow, mul_one,
    c.fiveOddPart_inf_centralizer_z hZ B5 q, B5Image_card hZ B5,
    ← v.fixed_card_eq c B5] at h
  simpa only [pow_two, mul_assoc] using h

/-- Transport the fixed odd subgroup into H using the actual z-class conjugator.
The odd-subgroup calculation for H remains an explicit earlier local input. -/
theorem fixed_card_cases
    (hoddH : ∀ A : Subgroup G, A ≤ d.toTypeRuSetup.H → Odd (Nat.card A) →
      Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5) :
    Nat.card (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G) = 1 ∨
      Nat.card (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G) = 3 ∨
      Nat.card (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G) = 5 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp v.z_class
  let f := (MulAut.conj g).toMonoidHom
  let A := fiveOddPart B5 ⊓ centralizer ({v.i} : Set G)
  have hcard : Nat.card (A.map f) = Nat.card A :=
    card_map_of_injective (MulAut.conj g).injective
  have hAH : A.map f ≤ d.toTypeRuSetup.H := by
    rintro y ⟨x, hx, rfl⟩
    rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff]
    change f v.i = c.z at hg
    rw [← hg, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hx.2]
  have hodd : Odd (Nat.card (A.map f)) := by
    rw [hcard]
    exact (fiveOddPart_odd B5).of_dvd_nat (card_dvd_of_le (show A ≤ fiveOddPart B5 from inf_le_left))
  simpa only [hcard] using hoddH (A.map f) hAH hodd

include v in
/-- The three numerical branches before the M₁₀ obstruction and non-Sylow step. -/
theorem oddPart_card_cases (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (q : FiveQuaternionData B5)
    (hoddH : ∀ A : Subgroup G, A ≤ d.toTypeRuSetup.H → Odd (Nat.card A) →
      Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5) :
    Nat.card (fiveOddPart B5) = 5 ∨ Nat.card (fiveOddPart B5) = 45 ∨
      Nat.card (fiveOddPart B5) = 125 := by
  have h := v.oddPart_card_formula c B5 hZ q
  rcases v.fixed_card_cases c B5 hoddH with h1 | h3 | h5
  · rw [h1] at h
    norm_num only [Nat.reducePow, Nat.reduceMul] at h
    exact Or.inl h
  · rw [h3] at h
    norm_num only [Nat.reducePow, Nat.reduceMul] at h
    exact Or.inr (Or.inl h)
  · rw [h5] at h
    norm_num only [Nat.reducePow, Nat.reduceMul] at h
    exact Or.inr (Or.inr h)

end FiveInverterData
end CFSG.Quasithin.ChapterJ.Centralizers.Choices
