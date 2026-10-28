module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime.Relations

/-!
# Excluding the defining prime from symplectic central-cover kernels

For every prime p > 3, a central extension of the literal Sp₄(Fₚ) splits
on its standard unipotent subgroup. Torus-equivariant additive root lifts
satisfy all six positive-root relations, and ordered matrix coordinates
construct the section. The subgroup has index (p²−1)(p⁴−1), prime to p.
Transfer therefore excludes p from the kernel of every finite perfect cover.
This argument includes p = 5 and assumes no multiplier or universality result.

Source: Aschbacher–Smith, A.2.2(2), printed p.33, and I.1.1–4,
printed pp.407–408; GLS3 §6.1, the type C₂ row of Table 6.1.2 and absence
of an exceptional multiplier for p > 3. The source's displayed I.1.4 list
omits the ordinary odd-prime symplectic row; no claim is inferred from that
omission. The result here is the defining-prime part of central closure of
Sp₄(Fₚ), for use in the independent prime-by-prime global-section assembly.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
variable {p : ℕ} [Fact p.Prime]

/-- A section over the standard unipotent subgroup, with its literal inclusion. -/
theorem exists_unipotent_section (hp : 3 < p)
    {E : Type*} [Group E] (f : E →* Sp (ZMod p))
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : unipotent (F := ZMod p) →* E,
      f.comp s = (unipotent (F := ZMod p)).subtype := by
  obtain ⟨L⟩ := positiveRootLifts_of_central_extension hp f hf hk
  exact L.exists_unipotent_section

/-- The defining prime does not divide the kernel of any finite perfect
central covering of the actual matrix group Sp₄(Fₚ), for every p ≥ 5. -/
theorem not_dvd_card_kernel (hp : 3 < p)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p))) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨L⟩ := positiveRootLifts_of_central_extension hp f.toMonoidHom
    f.surjective f.ker_le_center
  exact not_dvd_card_kernel_of_positive_root_lifts f L

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
