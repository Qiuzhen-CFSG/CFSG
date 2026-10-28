module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Split
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit
public import Theory.GroupTheory.PerfectCentralCoverTorusNormalizer

/-!
# Transfer from a torus normalizer for the ordinary G₂ three-primary kernel

An actual local configuration makes the full torus preimage abelian by
swapping its two generators. The ambient torus inverter then inverts the
derived subgroup of the full Sylow preimage. Central transfer excludes three
from every finite perfect central kernel, including the literal canonical
universal projection used by the multiplier table.

The split configuration is constructed for every finite field whose order is
one modulo three, with arbitrary three-adic valuation of its unit-group order.
In the source prime-field range, the descended nonsplit configuration supplies
the remaining p ≡ −1 modulo three case, so the three-primary exclusion is
unconditional.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddThreePrimary

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

/-- The concrete local normalizer configuration removes three from every
finite perfect central covering of the actual octonion group. -/
theorem not_three_dvd_kernel_of_localData
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (D : LocalData F) :
    ¬ 3 ∣ Nat.card f.ker := by
  exact not_dvd_card_kernel_of_swapped_torus_normalizer f hf hk (by decide)
    D.sylow D.torus D.first D.second D.cycle D.inverter D.swap
    D.torus_generated D.generators_commute D.swap_first D.swap_second
    D.sylow_generated D.cycle_normalizes D.inverts_torus D.fixes_cycle

/-- Application to the literal canonical universal projection. Constructing
`LocalData F` remains necessary to obtain the unconditional source statement. -/
theorem universal_not_three_dvd_kernel_of_localData
    (hF : 2 < Nat.card F) (D : LocalData F) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hF
  exact not_three_dvd_kernel_of_localData (universalProjection (Model F))
    (universalProjection_surjective _) (universalProjection_ker_le_center _) D

/-- The split congruence class, with no restriction on the three-adic
valuation of the field-unit order. All local model premises are discharged. -/
theorem universal_not_three_dvd_kernel_of_split
    (hF : 2 < Nat.card F) (hd : 3 ∣ Nat.card F - 1) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  obtain ⟨D⟩ := exists_split_localData hd
  exact universal_not_three_dvd_kernel_of_localData hF D

/-- In the exact source prime-field range, the only remaining local input
is the nonsplit configuration. Its producer must supply actual model witnesses. -/
theorem prime_universal_not_three_dvd_kernel_of_nonsplit_data
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    (hnonsplit : 3 ∣ p + 1 → Nonempty (LocalData F)) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  have hlarge : 2 < Nat.card F := by omega
  by_cases hd : 3 ∣ p - 1
  · exact universal_not_three_dvd_kernel_of_split hlarge (hF ▸ hd)
  have hplus : 3 ∣ p + 1 := by
    have hnot : ¬ 3 ∣ p := by
      intro h
      have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp h
      omega
    rw [Nat.dvd_iff_mod_eq_zero] at hnot hd ⊢
    omega
  obtain ⟨D⟩ := hnonsplit hplus
  exact universal_not_three_dvd_kernel_of_localData hlarge D

/-- The ordinary G₂ three-primary multiplier exclusion in the complete odd
prime-field range.  The split branch uses the rational split torus, while the
nonsplit branch uses the descended norm-one torus and its Weyl normalizer. -/
theorem prime_universal_not_three_dvd_kernel
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  exact prime_universal_not_three_dvd_kernel_of_nonsplit_data hF hp
    (fun hd => exists_nonsplit_localData hF hp hd)

end Atlas.G2.MultiplierOrdinary.OddThreePrimary

end
