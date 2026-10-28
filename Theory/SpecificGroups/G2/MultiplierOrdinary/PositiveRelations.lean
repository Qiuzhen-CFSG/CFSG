module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.TorusEquivariance
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.ModelRelations
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.CommutingLifts
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.PolynomialLifts
public import Theory.SpecificGroups.G2.FiniteUniversalCover

/-!
# Positive-root relations and the ordinary G₂ defining-prime calculation

The actual six root sections can be chosen equivariantly for the entire split
torus in each source range. Scalar-equivariant uniqueness proves their ten
commuting and five polynomial relations in the cover, and collection gives
the complete ordered multiplication law. The resulting section of the literal
unipotent subgroup and central Sylow transfer exclude the defining prime from
the kernel of every finite perfect central cover, including the canonical one.

Both relation families are discharged on the same root-section system. The
even-field range requires more than four elements, and the prime-field range
requires a prime greater than three. The exceptional orders three and four
are not covered by these conclusions.

Source: Aschbacher–Smith A.2.2–A.2.4 (PDF p.44), I.1.3–I.1.4
(PDF pp.418–419), and GLS III §6.1. The octonion roots and torus formulas
are the attributed ATLAS ports used by the imported modules.
-/

public section
namespace Atlas.G2.MultiplierOrdinary
open PerfectCentralCovering
variable {F : Type*} [Field F] [Finite F]

/-- A torus-equivariant system on the actual universal cover in the ordinary
even-field range. -/
theorem even_universal_torusEquivariant_sections [CharP F 2]
    (hF : 4 < Nat.card F) :
    ∃ L : RootSections (universalProjection (Model F)), L.TorusEquivariant := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact even_torusEquivariant_sections hF (universalProjection (Model F))
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- The same literal system in the source odd-prime range. -/
theorem prime_universal_torusEquivariant_sections {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ L : RootSections (universalProjection (Model F)), L.TorusEquivariant := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact prime_torusEquivariant_sections hF (by omega) (universalProjection (Model F))
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- The pairwise equations discharge the multiplication premise of the
unipotent-section transfer theorem for the prescribed covering map. -/
theorem not_dvd_kernel_of_collectionRelations
    {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime] [CharP F p]
    (c : Cover E (Model F)) (L : RootSections c.toMonoidHom)
    (hL : L.CollectionRelations) : ¬ p ∣ Nat.card c.toMonoidHom.ker :=
  not_dvd_kernel_of_positive_relations c L (hL.productCompatible L)

/-- Application of collection and transfer to the literal canonical cover. -/
theorem universal_not_dvd_kernel_of_collectionRelations
    {p : ℕ} [Fact p.Prime] [CharP F p] (hF : 2 < Nat.card F)
    (L : RootSections (universalProjection (Model F)))
    (hL : L.CollectionRelations) :
    ¬ p ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hF
  exact not_dvd_kernel_of_collectionRelations (universalCover (Model F)) L hL

namespace RootSections

/-- Torus equivariance forces all fifteen inter-root equations on one system
of sections: the commuting family supplies the premise of the polynomial proof. -/
theorem TorusEquivariant.collectionRelations
    {E : Type*} [Group E] {f : E →* Model F}
    (L : RootSections f) (hL : L.TorusEquivariant) (hF : 4 < Nat.card F)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    L.CollectionRelations :=
  collectionRelations_of_torusEquivariant hF L hf hk hL
    (hL.commutingRelations L hF hf hk)

/-- Collection gives the literal six-coordinate product law, with no
inter-root relation left as an additional premise. -/
theorem TorusEquivariant.productCompatible
    {E : Type*} [Group E] {f : E →* Model F}
    (L : RootSections f) (hL : L.TorusEquivariant) (hF : 4 < Nat.card F)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    L.ProductCompatible :=
  (hL.collectionRelations L hF hf hk).productCompatible L

end RootSections

/-- The actual six positive roots lift compatibly through every finite
perfect central cover in the ordinary even-field range. -/
theorem even_cover_compatible_sections [CharP F 2] (hF : 4 < Nat.card F)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model F)) :
    ∃ L : RootSections c.toMonoidHom, L.ProductCompatible := by
  obtain ⟨L, hL⟩ := even_torusEquivariant_sections hF c.toMonoidHom
    c.surjective c.ker_le_center
  exact ⟨L, hL.productCompatible L hF c.surjective c.ker_le_center⟩

/-- The same compatible lifting for a prime field of order greater than
three; primality also excludes the field order four. -/
theorem prime_cover_compatible_sections {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model F)) :
    ∃ L : RootSections c.toMonoidHom, L.ProductCompatible := by
  have hp5 := (Fact.out : p.Prime).five_le_of_ne_two_of_ne_three (by omega) (by omega)
  obtain ⟨L, hL⟩ := prime_torusEquivariant_sections hF (by omega) c.toMonoidHom
    c.surjective c.ker_le_center
  exact ⟨L, hL.productCompatible L (by omega) c.surjective c.ker_le_center⟩

/-- Compatible positive-root sections of the literal canonical projection
in characteristic two, away from the exceptional order four. -/
theorem even_universal_compatible_sections [CharP F 2] (hF : 4 < Nat.card F) :
    ∃ L : RootSections (universalProjection (Model F)), L.ProductCompatible := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact even_cover_compatible_sections hF (universalCover (Model F))

/-- Compatible positive-root sections of the literal canonical projection
in the ordinary odd-prime range. -/
theorem prime_universal_compatible_sections {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ L : RootSections (universalProjection (Model F)), L.ProductCompatible := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact prime_cover_compatible_sections hF hp (universalCover (Model F))

/-- Splitting the actual unipotent subgroup excludes two from the kernel
of every finite perfect central cover in the ordinary even-field range. -/
theorem even_cover_not_two_dvd_kernel [CharP F 2] (hF : 4 < Nat.card F)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model F)) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨L, hL⟩ := even_cover_compatible_sections hF c
  exact not_dvd_kernel_of_positive_relations c L hL

/-- Defining-prime exclusion for an actual finite perfect central cover of
G₂ over a prime field. The characteristic follows from the field order. -/
theorem prime_cover_not_defining_dvd_kernel {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model F)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨L, hL⟩ := prime_cover_compatible_sections hF hp c
  exact not_dvd_kernel_of_positive_relations c L hL

/-- The defining prime is absent from the literal universal-cover kernel
in the ordinary even-field range. -/
theorem even_universal_not_two_dvd_kernel [CharP F 2] (hF : 4 < Nat.card F) :
    ¬ 2 ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact even_cover_not_two_dvd_kernel hF (universalCover (Model F))

/-- The defining prime is absent from the literal universal-cover kernel
in the ordinary odd-prime range, with every root-relation premise discharged. -/
theorem prime_universal_not_defining_dvd_kernel {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) :
    ¬ p ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact prime_cover_not_defining_dvd_kernel hF hp (universalCover (Model F))

/-- The source's `G₂(2ⁿ)`, `n ≥ 3`, formulation of the same exclusion. -/
theorem even_universal_not_two_dvd_kernel_of_card_pow
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n) :
    ¬ 2 ∣ Nat.card (universalProjection (Model F)).ker := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hpow : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  exact even_universal_not_two_dvd_kernel (by omega)

end Atlas.G2.MultiplierOrdinary
end
