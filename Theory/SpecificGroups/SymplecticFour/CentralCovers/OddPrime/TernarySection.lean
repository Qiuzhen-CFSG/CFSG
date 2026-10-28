module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.PrimeSupport
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary

/-!
# Assembling a section of a perfect central cover of Sp₄(3)

`PrimeSupport` excludes every prime except two and three from the kernel
of a finite perfect central cover of the literal matrix group. `TwoPrimary`
and `ThreePrimary` exclude the remaining primes using sections over actual
matrix subgroups and central transfer. Thus the kernel is trivial. Inverting
the given covering map produces a homomorphic section with the required
commuting equation.

`exists_section` discharges both prime exclusions in the retained conditional
assembly. It supplies the ternary input to
`OddPrime.isUniversal_of_prime_field_sections`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.4(1),
printed p.408, and GLS3 §6.1. The projective universal-cover and C₂-kernel
assembly belongs to `OddPrime.Assembly`.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection

/-- Excluding the two remaining primes gives a section of the specified
covering map, rather than only an abstract isomorphism of its groups. -/
theorem exists_section_of_not_two_dvd_of_not_three_dvd
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (OddPrime.Sp (ZMod 3)))
    (h2 : ¬ 2 ∣ Nat.card f.toMonoidHom.ker)
    (h3 : ¬ 3 ∣ Nat.card f.toMonoidHom.ker) :
    ∃ s : OddPrime.Sp (ZMod 3) →* E,
      f.toMonoidHom.comp s = MonoidHom.id _ := by
  have hk : f.toMonoidHom.ker = ⊥ := by
    apply Subgroup.card_eq_one.mp
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hd
    rcases prime_dvd_kernel_eq_two_or_three f hp hd with rfl | rfl
    · exact h2 hd
    · exact h3 hd
  let e : E ≃* OddPrime.Sp (ZMod 3) := MulEquiv.ofBijective f.toMonoidHom
    ⟨(f.toMonoidHom.ker_eq_bot_iff).mp hk, f.surjective⟩
  exact ⟨e.symm.toMonoidHom, MonoidHom.ext (fun x => e.apply_symm_apply x)⟩

/-- Every finite perfect central cover of the literal matrix group Sp₄(3)
has a homomorphic section commuting with its specified covering map. -/
theorem exists_section
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (OddPrime.Sp (ZMod 3))) :
    ∃ s : OddPrime.Sp (ZMod 3) →* E,
      f.toMonoidHom.comp s = MonoidHom.id _ :=
  exists_section_of_not_two_dvd_of_not_three_dvd f
    (TwoPrimary.not_two_dvd_kernel f) (ThreePrimary.not_three_dvd_kernel f)

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection
