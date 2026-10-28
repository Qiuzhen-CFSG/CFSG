module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.RootCompatibility
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow

/-!
# Central closure of odd symplectic four-space over prime fields

A prime in the central kernel of a finite perfect cover must divide the
actual matrix group order. For Sp₄(Fₚ), it is therefore p or divides p⁴−1.
Excluding the defining prime, two, and the other odd primes makes the given
projection bijective; its inverse is the required global homomorphic section.
The local consumer below obtains these exclusions from sections over actual
Sylow subgroups and abelian full preimages of the other Sylow subgroups.

For primes p > 3, `exists_section` discharges all three exclusions using
the positive-root unipotent section, the split and nonsplit torus and
quartic Sylow calculations, and the section on the plane-pair subgroup
of odd index. The conditional reductions remain available separately.

Source: Aschbacher–Smith, A.2.2(2), printed p.33, and I.1.1–I.1.4,
printed pp.407–408; GLS3 §6.1, especially the C₂ row of Table 6.1.2 and the
absence of an exceptional multiplier in this range. A.2.2 names PSp₄(p),
while the displayed I.1.4 list omits the ordinary odd-prime symplectic row;
the table is source guidance, not a Lean proof input.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections

variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Group E] [Finite E]

private theorem kernel_prime_dvd_base
    {G : Type*} [Group G] [Finite G]
    (f : PerfectCentralCovering.Cover E G)
    {r : ℕ} [Fact r.Prime] (hr : r ∣ Nat.card f.toMonoidHom.ker) : r ∣ Nat.card G := by
  by_contra h
  apply f.not_dvd_card_multiplier_of_isCyclic_sylow ?_ hr
  intro P
  have hc : Nat.card P = 1 := P.isPGroup'.card_eq_or_dvd.resolve_right
    (fun hP => h (hP.trans (P : Subgroup G).card_subgroup_dvd_card))
  let : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hc).1
  infer_instance

/-- Prime support of the actual central kernel, using the matrix group order. -/
theorem kernel_prime_support
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    {r : ℕ} [Fact r.Prime] (hr : r ∣ Nat.card f.toMonoidHom.ker) :
    r = p ∨ r ∣ p ^ 4 - 1 := by
  have hd := kernel_prime_dvd_base f hr
  change r ∣ Nat.card (Theory.SpecificGroups.SymplecticFour.Sp (ZMod p)) at hd
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, Nat.card_zmod] at hd
  rcases (Fact.out : r.Prime).dvd_mul.mp hd with hd | hd
  · rcases (Fact.out : r.Prime).dvd_mul.mp hd with hd | hd
    · exact Or.inl (((Nat.dvd_prime (Fact.out : p.Prime)).mp
        ((Fact.out : r.Prime).dvd_of_dvd_pow hd)).resolve_left
          (Fact.out : r.Prime).ne_one)
    · right
      have he : p ^ 4 - 1 = (p ^ 2 - 1) * (p ^ 2 + 1) := by
        calc
          p ^ 4 - 1 = (p ^ 2) ^ 2 - 1 := by congr 1; ring
          _ = _ := by simpa [mul_comm] using Nat.sq_sub_sq (p ^ 2) 1
      rw [he]
      exact dvd_mul_of_dvd_left hd _
  · exact Or.inr hd

/-- Assemble the three independent kernel exclusions into an actual section. -/
theorem exists_section_of_prime_exclusions
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hdef : ¬ p ∣ Nat.card f.toMonoidHom.ker)
    (htwo : ¬ 2 ∣ Nat.card f.toMonoidHom.ker)
    (hodd : ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p → r ∣ p ^ 4 - 1 →
      ¬ r ∣ Nat.card f.toMonoidHom.ker) :
    ∃ s : Sp (ZMod p) →* E, f.toMonoidHom.comp s = MonoidHom.id _ := by
  have hc : Nat.card f.toMonoidHom.ker = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro r hr hdiv
    by_cases hrp : r = p
    · subst r; exact hdef hdiv
    by_cases hr2 : r = 2
    · subst r; exact htwo hdiv
    let : Fact r.Prime := ⟨hr⟩
    exact hodd r hr hr2 hrp ((kernel_prime_support f hdiv).resolve_left hrp) hdiv
  let e : E ≃* Sp (ZMod p) := MulEquiv.ofBijective f.toMonoidHom
    ⟨f.toMonoidHom.ker_eq_bot_iff.mp (Subgroup.card_eq_one.mp hc), f.surjective⟩
  exact ⟨e.symm.toMonoidHom, MonoidHom.ext fun x => e.apply_symm_apply x⟩

/-- A concrete local-to-global consumer: all sections use literal subgroup
inclusions, and the odd-prime hypothesis concerns full Sylow preimages. -/
theorem exists_section_of_local_splittings
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hdef : ∃ P : Sylow p (Sp (ZMod p)), ∃ s : P →* E,
      f.toMonoidHom.comp s = (P : Subgroup (Sp (ZMod p))).subtype)
    (htwo : ∃ P : Sylow 2 (Sp (ZMod p)), ∃ s : P →* E,
      f.toMonoidHom.comp s = (P : Subgroup (Sp (ZMod p))).subtype)
    (hodd : ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p → r ∣ p ^ 4 - 1 →
      ∃ P : Sylow r (Sp (ZMod p)),
        IsMulCommutative ((P : Subgroup (Sp (ZMod p))).comap f.toMonoidHom)) :
    ∃ s : Sp (ZMod p) →* E, f.toMonoidHom.comp s = MonoidHom.id _ := by
  obtain ⟨P, s, hs⟩ := hdef
  obtain ⟨Q, t, ht⟩ := htwo
  apply exists_section_of_prime_exclusions f
    (PerfectCentralCovering.not_dvd_card_kernel_of_section f _ P.not_dvd_index s hs)
    (PerfectCentralCovering.not_dvd_card_kernel_of_section f _ Q.not_dvd_index t ht)
  intro r hr hr2 hrp hdiv
  let : Fact r.Prime := ⟨hr⟩
  let := f.isPerfect
  obtain ⟨R, hR⟩ := hodd r hr hr2 hrp hdiv
  exact PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow_preimage
    f.toMonoidHom f.surjective f.ker_le_center R hR

/-- Every finite perfect central cover of the literal matrix group Sp₄(Fₚ)
splits for p > 3, including p = 5. The three local prime exclusions make
the projection bijective, whose inverse is the global section. -/
theorem exists_section (hp : 3 < p)
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p))) :
    ∃ s : Sp (ZMod p) →* E, f.toMonoidHom.comp s = MonoidHom.id _ := by
  apply exists_section_of_prime_exclusions f
    (DefiningPrime.not_dvd_card_kernel hp f)
    (TwoPrimary.not_dvd_card_kernel hp f)
  intro r hr hr2 hrp hd
  let : Fact r.Prime := ⟨hr⟩
  exact OddNondefining.not_dvd_card_kernel hp hr2 hrp hd f

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections
