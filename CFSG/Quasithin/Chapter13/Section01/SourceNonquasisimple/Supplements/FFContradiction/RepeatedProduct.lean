module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OddSection
public import Theory.Representation.ProductIsotypic.Nonabelian

/-!
# Constructing the repeated constituent in the odd-prime exclusion

An irreducible action of the two commuting source factors restricts
homogeneously to K_B A. Clifford's theorem supplies an actual irreducible
constituent and equivariant coordinates. The nonabelian action of L_R
forces more than one copy by finite Schur theory. The repeated-section
budget then supplies the FF inequality and B.5.6 excludes the odd branch.

The common chief section and its marked factor actions still have to be
constructed by qt-d-1319-ff-contradiction. This module does not assume the
multiplicity, coordinates, FF inequality, or classification conclusion.
The literal candidate application retains its original hat representation.
Source: Aschbacher--Smith 13.1.9, printed pp.870--871, preceding (*).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.RepeatedSectionBudget
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
namespace OddSection
universe u
variable {Q V : Type u} [Group Q] [Finite Q]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Structural data on the chosen chief section and its two marked commuting
factors, before any constituent or multiplicity has been selected. -/
structure ProductData (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) where
  overgroup : Subgroup Q
  actor_le : A ≤ overgroup
  actor_rank : rank A ≤ 2
  lower : Subrepresentation (ρ.comp overgroup.subtype)
  upper : Subrepresentation (ρ.comp overgroup.subtype)
  lower_le_upper : lower ≤ upper
  Factor : Type u
  [factorGroup : Group Factor]
  action : Representation (ZMod 2) (overgroup × Factor)
    (upper.toSubmodule ⧸ (sectionLower (ρ.comp overgroup.subtype) lower upper).toSubmodule)
  irreducible : IsIrreducible action
  first_action : ∀ g v, action (g,1) v =
    sectionRepresentation (ρ.comp overgroup.subtype) lower upper g v
  noncommuting : ∃ a b : Factor, action (1,a*b) ≠ action (1,b*a)
  moves : RepeatedSectionBudget.actor ρ overgroup A lower upper ≠ ⊥
  oddSubgroup : Subgroup overgroup
  [oddNormal : oddSubgroup.Normal]
  prime : ℕ
  prime_prime : prime.Prime
  prime_gt_three : 3 < prime
  odd_group : IsPGroup prime oddSubgroup
  two_quotient : IsPGroup 2 (overgroup ⧸ oddSubgroup)

attribute [instance] ProductData.factorGroup ProductData.oddNormal

omit [Finite Q] in
/-- Construct the constituent and repeated coordinates from the marked
irreducible product action; finite Schur theory proves the multiplicity bound. -/
theorem ProductData.exists_repeated {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q}
    (d : ProductData ρ A) : Nonempty (Data ρ A) := by
  let := d.irreducible
  obtain ⟨S,hS,r,hr,e,he⟩ := ProductIsotypic.exists_multiple_copy_coordinates
    d.action d.noncommuting
  exact ⟨{
    overgroup := d.overgroup
    actor_le := d.actor_le
    actor_rank := d.actor_rank
    lower := d.lower
    upper := d.upper
    lower_le_upper := d.lower_le_upper
    Space := S.toSubmodule
    representation := S.toRepresentation
    irreducible := hS
    multiplicity := r
    multiple := hr
    coordinates := e
    intertwines := fun g v => by rw [←d.first_action]; exact he g v
    moves := d.moves
    oddSubgroup := d.oddSubgroup
    prime := d.prime
    prime_prime := d.prime_prime
    prime_gt_three := d.prime_gt_three
    odd_group := d.odd_group
    two_quotient := d.two_quotient }⟩
omit [Finite Q] in
/-- Transport the exclusion after constructing the repeated coordinates. This
fixed-representation boundary also keeps the literal quotient consumer small. -/
theorem product_isEmpty_of_repeated {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q}
    (h : IsEmpty (Data ρ A)) : IsEmpty (ProductData ρ A) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨s⟩ := d.exists_repeated
  exact h.false s

end OddSection

open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The marked irreducible product action on a section of the literal hat module. -/
abbrev OddProductSection (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)] :=
  OddSection.ProductData (Q := HatGroup T L Y j)
    (V := Additive (commonModule T L Y j)) (hatRepresentation T L Y j) (hatImage T L Y j A)

/-- The source candidate excludes the odd product section without assuming
an irreducible constituent, repeated coordinates, or their multiplicity. -/
theorem candidate_excludes_odd_product_section (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (ChapterB.thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G)) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ⁅⁅omegaClosure T L Y j,canonicalSupplement T L⁆,thompsonCommutator T L Y j⁆ ≠ ⊥ ∧
      ∃ n : (commonModule T L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule T L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          ThompsonActorAlternative (T : Subgroup G) L Y j ∧
          ∀ A ∈ ChapterB.thompsonFamily (radicalSylowCentralizer T L) j,
            hatImage T L Y j A ≠ ⊥ → IsEmpty (OddProductSection (T : Subgroup G) L Y A j) := by
  obtain ⟨Y,w,hm,n,he⟩ := candidate_excludes_odd_repeated_section h hmany hs hrig hclass
    hL hn hH hTH hne hC hAC hj hN
  let := n
  obtain ⟨e,ha,hactor,hno⟩ := he
  let := e
  refine ⟨Y,w,hm,n,e,ha,hactor,?_⟩
  intro A hA hAn
  exact OddSection.product_isEmpty_of_repeated (hno A hA hAn)
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
