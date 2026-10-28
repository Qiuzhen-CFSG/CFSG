module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Cases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankInequality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Completion

/-!
# Paired offenders in the characteristic-two branch

The four minimal-best-offender geometries on the natural S8 module and their
actual ranks and fixed codimensions are proved in `Cases`. The given natural
action transports them to centralizers in the ambient group and in the local
parabolic group. Sylow conjugacy supplies a nonempty minimal family from the
component in J(I); the genuine identification L* = A8 discharges noncentrality.
In the surviving disjoint-transposition case, an odd permutation excludes the
minimal action image from the even image of S0.

`B2Lifting` proves the maximum-image and constructive replacement clauses for
both restricted natural actions. `Completion` assembles paired minimality,
the literal XT/O₂(XT) quotient calculations, and the paired rank inequality.
It excludes the semidihedral extension and cases (i),(ii),(iv), constructs the
maximum replacement in C_I(U_L), and proves T-normalization of the actual S₀.
The nonempty minimal family follows from the noncentral component of J(I).
Its `Geometry.conclusions` gives the minimal-image exclusion, replacement,
and Thompson equality; `Geometry.outside_contradiction` applies the earlier
uniqueness theorem and discharges the terminal source argument.

These are conditional results under the genuine 15.3.32 configuration and
compatible action/quotient identifications, which the source assembly owner
constructs. No rank tuple, B.2 lifting clause, paired-minimality conclusion,
or Thompson-containment premise is assumed by the new assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Theorem 15.3.25, printed pp.1133–1134 (PDF pp.1150–1151).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup Stellmacher Representation.BinaryOffender BinaryPermutation
variable {G : Type*} [Group G]

/-- The actual action images have the four source geometries and their computed
dimensions, conditional on B.2.5's best-offender and equal-weight lift clauses. -/
theorem minimal_image_cases_and_dimensions {I U : Subgroup G}
    (d : NaturalEightAction I U) (S A : Subgroup I)
    (hA : A ∈ minimalNontrivialActionFamily S d.actor)
    (hbest : ∀ B ∈ elementaryAbelianMaxSubgroups S, B.map d.actor ≠ ⊥ →
      IsBestOffender (naturalRepresentation (Fin 8)) (B.map d.actor))
    (hlift : ∀ B ∈ elementaryAbelianMaxSubgroups S, ∀ E,
      IsElementaryTwo E → EqualWeightLE (naturalRepresentation (Fin 8)) E (B.map d.actor) →
      ∃ D ∈ elementaryAbelianMaxSubgroups S, D.map d.actor = E) :
    ∃ c : EightCase, c.Realizes (A.map d.actor) ∧
      rank (A.map d.actor) = c.actorRank ∧
      rank U - rank (U ⊓ centralizer ((A.map I.subtype : Subgroup G) : Set G)) = c.codim := by
  obtain ⟨c, hc⟩ := minimalBest_realizes
    (minimal_action_image_isMinimalBest S A d.actor _ hA hbest hlift)
  have hd := EightCase.dimensions hc
  exact ⟨c, hc, hd.1, (d.fixedCodim_eq_rank_sub A).symm.trans hd.2⟩

/-- In case (iii), exclusion holds for the action images themselves, as required
by `thompson_le_kernel_of_minimal_images`. -/
theorem disjoint_image_not_le_even_image
    (A S0 : Subgroup G) (f : G →* Equiv.Perm (Fin 8))
    (hA : EightCase.disjoint.Realizes (A.map f))
    (hS0 : S0.map f ≤ alternatingGroup (Fin 8)) :
    ¬ A.map f ≤ S0.map f :=
  fun h => EightCase.disjoint_not_le_alternating hA (h.trans hS0)

variable [Finite G]

/-- The component of J(I) supplies the nonempty minimal family whenever it
acts nontrivially on its actual commutator module. No nonemptiness assumption
is added to the local configuration. -/
theorem component_minimal_family_nonempty
    (d : LocalData G) (I : Subgroup G) (c : ComponentWitness d I)
    (a : NaturalEightAction I (d.componentModule I c.L)) (S : Sylow 2 I)
    (hnoncentral : ¬ c.L ≤ centralizer (d.componentModule I c.L : Set G)) :
    (minimalNontrivialActionFamily (S : Subgroup I) a.actor).Nonempty := by
  apply minimal_action_family_nonempty_of_component I c.L S a.actor c.le_thompson
  intro hL
  exact hnoncentral (hL.trans a.ker_le_centralizer)

/-- The genuine identification L* = A8 already ensures the source family
is nonempty, with no separate noncentrality premise. -/
theorem component_minimal_family_nonempty_of_alternating_image
    (d : LocalData G) (I : Subgroup G) (c : ComponentWitness d I)
    (a : NaturalEightAction I (d.componentModule I c.L)) (S : Sylow 2 I)
    (himage : (c.L.subgroupOf I).map a.actor = alternatingGroup (Fin 8)) :
    (minimalNontrivialActionFamily (S : Subgroup I) a.actor).Nonempty := by
  apply minimal_action_family_nonempty_of_component I c.L S a.actor c.le_thompson
  intro hL
  have hsub : c.L.subgroupOf I ≤ a.actor.ker := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hL hx
    have he' : y = x := I.subtype_injective he
    exact he' ▸ hy
  have hbot : alternatingGroup (Fin 8) = ⊥ :=
    himage.symm.trans ((Subgroup.map_eq_bot_iff _).mpr hsub)
  let k : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3
  have hk : k ∈ alternatingGroup (Fin 8) := by
    change Equiv.Perm.sign k = 1
    decide +kernel
  rw [hbot] at hk
  exact (by decide +kernel : k ≠ 1) hk

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
