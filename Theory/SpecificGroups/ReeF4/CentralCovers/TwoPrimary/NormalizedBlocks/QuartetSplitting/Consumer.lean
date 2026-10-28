module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks

/-!
# The quartet splitting application to torus-normalized Ree lifts

For m≥2 the nonabelian quartet sections are discharged by their actual Suzuki
Levi embeddings. The four additive sections remain explicit, as required by
the independent additive-block calculation. For m=1, only the ambient lifted
Suzuki triple-commutator premise remains in the nonabelian branch.

This uses the parent's literal assembly theorem, so its averaging retains
all internal multiplication laws. Source: Aschbacher–Smith I.1.1–4,
printed pp.407–408; GLS3 §6.1 and §§2.3–2.4.
-/

public section
namespace ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
open ElementaryTwoBound PerfectCentralCovering

/-- Actual parent application for all ordinary parameters. -/
theorem torusEquivariant_of_two_le_and_pair_sections (m : ℕ) (hm : 2 ≤ m)
    {F : Type*} [Group F] (d : Cover F (Model m))
    (hd : Nat.card d.toMonoidHom.ker = 2)
    (hp : ∀ j : Fin 4, ∃ s : X m (rootIndex (.inl j)) →* F,
      d.toMonoidHom.comp s = (X m (rootIndex (.inl j))).subtype) :
    ∃ L : BlockSections m d.toMonoidHom, L.TorusEquivariant :=
  exists_torusEquivariant_of_pair_and_quartet_sections m d hd hp
    (quartet_sections_of_two_le m hm d.toMonoidHom d.surjective d.ker_le_center)

/-- Complete parameter-range assembly, retaining precisely the independent
additive sections and the exceptional ambient triple-commutator obligation. -/
theorem torusEquivariant_of_pair_sections_and_small_class_two (m : ℕ) (hm : 1 ≤ m)
    {F : Type*} [Group F] [Finite F] (d : Cover F (Model m))
    (hd : Nat.card d.toMonoidHom.ker = 2)
    (hp : ∀ j : Fin 4, ∃ s : X m (rootIndex (.inl j)) →* F,
      d.toMonoidHom.comp s = (X m (rootIndex (.inl j))).subtype)
    (hc : m = 1 → LiftedRootClassTwo m d.toMonoidHom) :
    ∃ L : BlockSections m d.toMonoidHom, L.TorusEquivariant :=
  exists_torusEquivariant_of_pair_and_quartet_sections m d hd hp
    (quartet_sections_of_small_class_two m hm d.toMonoidHom d.surjective d.ker_le_center hc)

end ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
