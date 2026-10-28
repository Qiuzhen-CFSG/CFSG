module

public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.SpecificGroups.ReeF4.DerivedCarrier
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport

/-!
# Prime-degree local calculations for Ree central covers

The literal fixed positive subgroup in the concrete Ree model has odd index,
by the proved fixed Bruhat geometry. A section over this subgroup therefore
excludes two from a covering kernel. For odd primes the same transfer argument
uses an actual Sylow subgroup. The general prime-kernel quotient reduction
means that these local sections are needed only for covers of prime degree.

These theorems connect the two independent local lifting calculations to every
finite perfect central cover and to the canonical universal projection. The
section premises remain explicit: this module does not claim that the Ree
multiplier calculation has been completed. In particular, centrality, order,
perfectness, and the fixed-point construction alone do not supply the sections.

The canonical application requires m ≥ 1 and derives perfectness from the
two actual perfect seeds. No section is asserted at m = 0, and the full
binary fixed group is never identified with the Tits simple group.

Source: Aschbacher–Smith, I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`, referring to GLS3, Theorem 6.1.4 and Tables 6.1.2–3.
The fixed positive subgroup and its index use GLS3, Sections 2.3–2.4.
-/

public section

namespace ReeF4.CentralCovers

open Subgroup PerfectCentralCovering

universe u

/-- The subgroup used for the defining-prime transfer is the actual fixed
positive subgroup, with no Sylow or simplicity premise. -/
theorem unipotent_index_odd (m : ℕ) : Odd (Parabolics.unipotent m).index :=
  Parabolics.OuterLocal.LargeAutomorphisms.unipotent_index_odd_of_standard
    (canonicalLocalBlockInput m)
    (LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m))

/-- Splitting only the degree-two covers over the marked positive subgroup
removes the entire two-primary part of every finite covering kernel. -/
theorem not_two_dvd_kernel_of_prime_unipotent_sections (m : ℕ)
    (htwo : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F (Model m)),
      Nat.card d.toMonoidHom.ker = 2 →
        ∃ s : Parabolics.unipotent m →* F,
          d.toMonoidHom.comp s = (Parabolics.unipotent m).subtype)
    {E : Type u} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  apply c.not_dvd_card_kernel_of_prime_kernel_local_sections
  intro F _ _ d hd
  obtain ⟨s, hs⟩ := htwo F d hd
  exact ⟨Parabolics.unipotent m, s,
    (Nat.not_even_iff_odd.mpr (unipotent_index_odd m)) ∘ even_iff_two_dvd.mpr, hs⟩

/-- The Sylow subgroup and its local section are required on the literal Ree
carrier; transfer discharges the index condition. -/
theorem not_dvd_kernel_of_prime_sylow_sections (m : ℕ) {p : ℕ} [Fact p.Prime]
    (hsections : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F (Model m)),
      Nat.card d.toMonoidHom.ker = p →
        ∃ (P : Sylow p (Model m)) (s : P →* F),
          d.toMonoidHom.comp s = (P : Subgroup (Model m)).subtype)
    {E : Type u} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  apply c.not_dvd_card_kernel_of_prime_kernel_local_sections
  intro F _ _ d hd
  obtain ⟨P, s, hs⟩ := hsections F d hd
  exact ⟨P, s, P.not_dvd_index, hs⟩

/-- Combining the independent local prime-degree calculations controls every
finite perfect central cover, including kernels of mixed order. -/
theorem kernel_eq_bot_of_prime_local_sections (m : ℕ)
    (htwo : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F (Model m)),
      Nat.card d.toMonoidHom.ker = 2 →
        ∃ s : Parabolics.unipotent m →* F,
          d.toMonoidHom.comp s = (Parabolics.unipotent m).subtype)
    (hodd : ∀ (p : ℕ) (_hp : p.Prime), p ≠ 2 →
      ∀ (F : Type u) [Group F] [Finite F] (d : Cover F (Model m)),
        Nat.card d.toMonoidHom.ker = p →
          ∃ (P : Sylow p (Model m)) (s : P →* F),
            d.toMonoidHom.comp s = (P : Subgroup (Model m)).subtype)
    {E : Type u} [Group E] [Finite E] (c : Cover E (Model m)) :
    c.toMonoidHom.ker = ⊥ := by
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases he : p = 2
  · subst p
    exact not_two_dvd_kernel_of_prime_unipotent_sections m htwo c
  · exact not_dvd_kernel_of_prime_sylow_sections m (hodd p hp he) c

/-- Application to the canonical projection for the genuine large Ree model.
Finiteness and perfectness are discharged; only local sections remain inputs. -/
theorem universalProjection_ker_eq_bot_of_prime_local_sections (m : ℕ) (hm : 1 ≤ m)
    (htwo : ∀ (F : Type) [Group F] [Finite F] (d : Cover F (Model m)),
      Nat.card d.toMonoidHom.ker = 2 →
        ∃ s : Parabolics.unipotent m →* F,
          d.toMonoidHom.comp s = (Parabolics.unipotent m).subtype)
    (hodd : ∀ (p : ℕ) (_hp : p.Prime), p ≠ 2 →
      ∀ (F : Type) [Group F] [Finite F] (d : Cover F (Model m)),
        Nat.card d.toMonoidHom.ker = p →
          ∃ (P : Sylow p (Model m)) (s : P →* F),
            d.toMonoidHom.comp s = (P : Subgroup (Model m)).subtype) :
    (universalProjection (Model m)).ker = ⊥ := by
  let : Group.IsPerfect (Model m) := ⟨DerivedCarrier.derived_eq_top hm⟩
  exact kernel_eq_bot_of_prime_local_sections m htwo hodd (universalCover (Model m))

end ReeF4.CentralCovers
