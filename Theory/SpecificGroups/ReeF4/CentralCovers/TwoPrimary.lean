module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.BlockCollection
public import Theory.SpecificGroups.ReeF4.CentralCovers.PrimaryReduction

/-!
# The defining-prime local lifting calculation for Ree covers

The concrete positive subgroup is the product of eight actual root blocks.
The four B₂ blocks retain their nonabelian laws. Homomorphic block lifts,
together with normalization of successive tails in the source root order,
give a section over that subgroup by the proved finite-order argument.

This connects the two independent calculations to the existing prime-kernel
reduction: constructing torus-equivariant block lifts, and proving their
inter-block relations. Both inputs remain explicit. In particular this
module does not yet assert the degree-two section theorem or the Ree
multiplier calculation. The source applications of the missing calculations
must retain m ≥ 1; the Tits endpoint is a separate group and proof.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`; GLS3 §6.1 and §§2.3–2.4.
-/

public section
namespace ReeF4.CentralCovers.TwoPrimary
open PerfectCentralCovering
universe u

/-- The precise local triangle consumed by PrimaryReduction, conditional on
individual block lifts and their actual inter-block relations. -/
theorem prime_unipotent_section_of_block_calculations (m : ℕ)
    {F : Type u} [Group F] [Finite F] (d : Cover F (Model m))
    (hlifts : ∃ L : BlockSections m d.toMonoidHom, L.TorusEquivariant)
    (hrelations : ∀ L : BlockSections m d.toMonoidHom,
      L.TorusEquivariant → L.NormalizesTails) :
    ∃ s : Parabolics.unipotent m →* F,
      d.toMonoidHom.comp s = (Parabolics.unipotent m).subtype := by
  obtain ⟨L,hL⟩ := hlifts
  exact L.exists_unipotent_section (hrelations L hL)

/-- Prime-degree local block calculations discharge all two-primary kernels,
using the parent-owned quotient reduction and transfer without extra indices. -/
theorem not_two_dvd_kernel_of_block_calculations (m : ℕ)
    (hlifts : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F (Model m)),
      Nat.card d.toMonoidHom.ker = 2 →
        ∃ L : BlockSections m d.toMonoidHom, L.TorusEquivariant)
    (hrelations : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F (Model m)),
      Nat.card d.toMonoidHom.ker = 2 →
        ∀ L : BlockSections m d.toMonoidHom, L.TorusEquivariant → L.NormalizesTails)
    {E : Type u} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  apply not_two_dvd_kernel_of_prime_unipotent_sections m _ c
  intro F _ _ d hd
  exact prime_unipotent_section_of_block_calculations m d
    (hlifts F d hd) (hrelations F d hd)

end ReeF4.CentralCovers.TwoPrimary
