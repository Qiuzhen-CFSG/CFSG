module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Data
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate
public import Theory.SpecificGroups.Held.Model.Perfect
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation

/-!
# The concrete Held representative is self-normalizing

A normalizing element carries each orbit of the actual four-word representative
bijectively onto another orbit. Held's perfectness makes its permutation sign
trivial, so the normalizer embeds in the even symmetries of the graph colored
by orbit size. The existing generator checks supply graph preservation.

A short word in the representative fixes vertex 4 and moves vertex 0; both
claims are checked in the kernel. A 512-point orbit at vertex 4 therefore gives
at least 1024 elements by orbit–stabilizer. An upper bound of 1024 on the even
colored graph group then forces the representative to equal its normalizer.

The checked orbit-size identification and colored graph bound discharge both
finite premises in `normalizer_eq`. No two-group, center, simplicity or outer
quotient hypothesis is needed. This module imports Representative directly,
independently of Calculations, which owns the subsequent Sylow assembly.
Source context: GLS3 Table 5.3p and the original ATLAS HeG1-p2058B0 carrier.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
open Subgroup

private def orbitMap (g : He) (hg : g ∈ normalizer (representative : Set He))
    (x : Fin 2058) : MulAction.orbit representative x →
      MulAction.orbit representative (g • x) := fun y =>
  ⟨g • y.val, by
    obtain ⟨p, hp⟩ := y.property
    change p.val • x = y.val at hp
    refine ⟨⟨g * p.val * g⁻¹, (mem_normalizer_iff.mp hg p.val).mp p.property⟩, ?_⟩
    change (g * p.val * g⁻¹) • (g • x) = g • y.val
    simpa only [mul_smul, inv_smul_smul] using congrArg (g • ·) hp⟩

/-- Conjugation by a normalizing element preserves the sizes of actual orbits. -/
public theorem orbit_card_normalizer_invariant (g : He)
    (hg : g ∈ normalizer (representative : Set He)) (x : Fin 2058) :
    Nat.card (MulAction.orbit representative (g • x)) =
      Nat.card (MulAction.orbit representative x) := by
  have hb (k : He) (hk : k ∈ normalizer (representative : Set He)) (y : Fin 2058) :
      Nat.card (MulAction.orbit representative y) ≤
        Nat.card (MulAction.orbit representative (k • y)) := by
    apply Nat.card_le_card_of_injective (orbitMap k hk y)
    intro u v huv
    apply Subtype.ext
    exact (MulAction.injective k) (congrArg Subtype.val huv)
  exact le_antisymm (by simpa using hb g⁻¹ (inv_mem hg) (g • x)) (hb g hg x)

set_option maxRecDepth 4096 in
/-- The orbit-cardinality table places the actual Held normalizer in the even
colored graph group. Graph preservation and parity need no extra premises. -/
public theorem normalizer_mem_evenColoredGraphGroup
    (horbits : ∀ x : Fin 2058,
      orbitSizeLabel x = Nat.card (MulAction.orbit representative x))
    (g : He) (hg : g ∈ normalizer (representative : Set He)) :
    representation g ∈ evenColoredGraphGroup := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
  · intro x
    rw [horbits, horbits]
    exact orbit_card_normalizer_invariant g hg x
  · exact hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g

private def stabilizerWitness : representative :=
  let s (i : Fin 4) : representative := ⟨generator i, generator_mem i⟩
  (s 1)⁻¹ * (s 2)⁻¹ * (s 1)⁻¹ * s 0 * s 1 * s 2 * s 1

set_option maxRecDepth 16384 in
private theorem stabilizerWitness_fixed :
    representation stabilizerWitness.val (4 : Fin 2058) = 4 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem stabilizerWitness_moved :
    representation stabilizerWitness.val (0 : Fin 2058) ≠ 0 := by decide +kernel

/-- The certified nonidentity stabilizer word doubles the 512-point orbit bound. -/
public theorem representative_card_ge_of_orbit_card
    (hcard : Nat.card (MulAction.orbit representative (4 : Fin 2058)) = 512) :
    1024 ≤ Nat.card representative := by
  let w : MulAction.stabilizer representative (4 : Fin 2058) :=
    ⟨stabilizerWitness, stabilizerWitness_fixed⟩
  have hw : w ≠ 1 := by
    intro hw
    apply stabilizerWitness_moved
    have he := congrArg (fun g : MulAction.stabilizer representative (4 : Fin 2058) =>
      representation g.val.val (0 : Fin 2058)) hw
    exact he
  let : Nontrivial (MulAction.stabilizer representative (4 : Fin 2058)) := ⟨⟨w, 1, hw⟩⟩
  have hl : 1 < Nat.card (MulAction.stabilizer representative (4 : Fin 2058)) := Finite.one_lt_card
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup representative (4 : Fin 2058))
  rw [Nat.card_prod, hcard] at he
  omega

/-- Identifying the published labels gives the required lower bound on P. -/
public theorem representative_card_ge_of_orbit_labels
    (horbits : ∀ x : Fin 2058,
      orbitSizeLabel x = Nat.card (MulAction.orbit representative x)) :
    1024 ≤ Nat.card representative := by
  apply representative_card_ge_of_orbit_card
  rw [← horbits]
  decide +kernel

/-- Normalizer equality from the two independent finite certificates. -/
public theorem normalizer_eq_of_orbit_certificates
    (horbits : ∀ x : Fin 2058,
      orbitSizeLabel x = Nat.card (MulAction.orbit representative x))
    (hupper : Nat.card evenColoredGraphGroup ≤ 1024) :
    normalizer (representative : Set He) = representative := by
  have hcard : Nat.card (normalizer (representative : Set He)) ≤
      Nat.card evenColoredGraphGroup := by
    apply Nat.card_le_card_of_injective
      (fun g : normalizer (representative : Set He) =>
        (⟨representation g.val,
          normalizer_mem_evenColoredGraphGroup horbits g.val g.property⟩ : evenColoredGraphGroup))
    intro g h he
    apply Subtype.ext
    apply representation_injective
    exact congrArg (fun z : evenColoredGraphGroup => z.val) he
  exact (eq_of_le_of_card_ge le_normalizer
    ((hcard.trans hupper).trans (representative_card_ge_of_orbit_labels horbits))).symm

/-- The subgroup generated by the four published Held words is self-normalizing
in the actual Held carrier. Both finite certificate premises are discharged. -/
public theorem normalizer_eq :
    normalizer (representative : Set He) = representative :=
  normalizer_eq_of_orbit_certificates
    orbitSizeLabel_eq_card_orbit evenColoredGraphGroup_card_le

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
