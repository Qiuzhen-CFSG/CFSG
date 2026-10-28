module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.Representatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.OuterSylow
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.OuterObstructions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions

/-!
# The four normal elementary outer Held rows

The full automorphism stabilizer is covered by 2048 concrete words. Kernel-checked
square and conjugate-commutation obstructions eliminate its entire outer coset.
Consequently every normal elementary subgroup lies in the inner pure subgroup.
The normal-index-two extension criterion then reduces exhaustive four-row coverage
to the 5120 one-element extensions by inner words from the five nodes (bottom and
the four published rows).

The checked inner extension calculation discharges every remaining finite branch.
The final theorem identifies every nontrivial normal elementary subgroup with
one of the four literal rows, under just realization and the quotient bound.
It supplies the elementary-coverage input to the proper-extension local cover;
the ambient normalizer inclusions and the source 15.3.42 assembly are separate.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
`Coverage/source/README.md` and `ElementaryCatalogue/source/README.md`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData
open ElementaryCatalogue

/-- Every normal elementary subgroup of the full stabilizer is contained in
its actual inner pure subgroup. No finite inner subgroup catalogue is used. -/
theorem normal_elementary_le_inner_pureTwo
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (E : Subgroup (MulAut Held.He)) (hle : E ≤ outerRepresentative)
    (hn : (E.subgroupOf outerRepresentative).Normal) (he : IsElementaryAbelian 2 E) :
    E ≤ pureTwo.map MulAut.conj := by
  let := he
  have he' : IsElementaryAbelian 2 (E.subgroupOf outerRepresentative) :=
    IsElementaryAbelian.subgroupOf hle
  intro x hx
  obtain ⟨⟨b, n⟩, h⟩ := element_surjective hreal hbound ⟨x, hle hx⟩
  have hx' : element (b, n) ∈ E.subgroupOf outerRepresentative := by
    rw [h]
    exact hx
  cases b
  · have hm : (element (false, n)).val ∈ pureTwo.map MulAut.conj := by
      change MulAut.conj (pureElement n).val * 1 ∈ pureTwo.map MulAut.conj
      rw [mul_one]
      exact mem_map_of_mem _ (pureElement n).property
    have hv := congrArg Subtype.val h
    change (element (false, n)).val = x at hv
    rwa [hv] at hm
  · exact (outer_element_not_mem n (E.subgroupOf outerRepresentative) hn he' hx').elim

/-- Conditional assembly from the remaining 5120 finite inner extensions.
The outer-coset exclusions and full word cover are already proved. -/
theorem normal_elementary_eq_ambientRow_of_inner_extensions
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hinner : ∀ (i : Option (Fin 4)) (n : Fin 1024),
      (extension i (false, n)).Normal → IsElementaryAbelian 2 (extension i (false, n)) →
      ∃ j : Option (Fin 4), extension i (false, n) = node j)
    (E : Subgroup (MulAut Held.He)) (hE : E ≠ ⊥) (hle : E ≤ outerRepresentative)
    (hn : (E.subgroupOf outerRepresentative).Normal) (he : IsElementaryAbelian 2 E) :
    ∃ j : Fin 4, E = ambientRow j := by
  let := he
  have he' : IsElementaryAbelian 2 (E.subgroupOf outerRepresentative) :=
    IsElementaryAbelian.subgroupOf hle
  obtain ⟨S, hS⟩ := outerRepresentative_sylow hreal hbound
  have hp : IsPGroup 2 outerRepresentative := by
    rw [← hS]
    exact S.isPGroup'
  have hstep : ∀ i n, (node i ⊔ zpowers (element n)).Normal →
      IsElementaryAbelian 2 ↥(node i ⊔ zpowers (element n)) →
      ∃ j, node i ⊔ zpowers (element n) = node j := by
    rintro i ⟨b, n⟩ hnormal helem
    cases b
    · exact hinner i n hnormal helem
    · exact (outer_element_not_mem n (extension i (true, n))
        hnormal helem (element_mem_extension i (true, n))).elim
  obtain ⟨j, hj⟩ :=
    Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.eq_node_of_normal_elementary_extensions
      hp node element (element_surjective hreal hbound) ⟨none, rfl⟩ hstep
      (E.subgroupOf outerRepresentative) hn he'
  have hm := congrArg (Subgroup.map outerRepresentative.subtype) hj
  rw [map_subgroupOf_eq_of_le hle] at hm
  cases j with
  | none => exact (hE (by simpa only [node, Subgroup.map_bot] using hm)).elim
  | some j => exact ⟨j, hm.trans (node_map_subtype j)⟩

/-- Every nontrivial elementary subgroup normal in the full outer Held Sylow
is one of the four published inner-automorphism rows. The finite word cover,
outer exclusions and inner extension certificates discharge all coverage premises. -/
theorem normal_elementary_eq_ambientRow
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (E : Subgroup (MulAut Held.He)) (hE : E ≠ ⊥) (hle : E ≤ outerRepresentative)
    (hn : (E.subgroupOf outerRepresentative).Normal) (he : IsElementaryAbelian 2 E) :
    ∃ j : Fin 4, E = ambientRow j :=
  normal_elementary_eq_ambientRow_of_inner_extensions hreal hbound
    inner_extensions E hE hle hn he

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData
