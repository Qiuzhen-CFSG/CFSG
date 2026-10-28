module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Branches
public import Theory.Representation.BinaryOffender.RepeatedSectionBudget
public import Theory.Representation.BinaryOffender.QuasisimpleImage
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ThreeFree

/-!
# The FF inequality and the odd-prime chief-section exclusion

Apply the repeated-section budget to the original hat action of the escaping
configuration. A nontrivial actor of rank at most two loses at most one rank
on the section; multiplicity greater than one therefore gives an FF-module
on the actual constituent image. Irreducibility removes its two-core, and
B.5.6 rules out a normal d-subgroup with two-group quotient for d > 3.

The SQTK cover is constructed from the original candidate maximal two-local,
through the literal common group and centralizer quotient. The final consumer
uses the same escaping Y, Thompson subgroup, omega closure and quotient maps.
No FF inequality or classification outcome is an input.

This proves the conditional section exclusion, not the full contradiction of
13.1.9. The controlled index, common chief section, repeated coordinates and
multiplicity must still be constructed by qt-d-1319-ff-contradiction, which also
owns the tensor identification and final generation. Earlier canonical stars
and source premises are discharged by qt-d-1317-supplements and qt-d-1317-source.
Source: Aschbacher--Smith, 13.1.9, printed pp.870--871.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.RepeatedSectionBudget
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction

namespace OddSection
open ChapterB.SourceInduction
universe u v
variable {Q : Type u} [Group Q] [Finite Q]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {I : Type u} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
  {ρ : Representation (ZMod 2) Q V} {E A : Subgroup Q}

private def imageCover (c : SQTKQuotient KnownSimple.IsKnownSimple E)
    (τ : Representation (ZMod 2) E I) : SQTKQuotient KnownSimple.IsKnownSimple (actionImage τ) where
  Cover := c.Cover
  kernel := ((actionHom τ).comp c.projection).ker
  sqtk := c.sqtk
  equiv := QuotientGroup.quotientKerEquivOfSurjective _
    (τ.asGroupHom.rangeRestrict_surjective.comp c.projection_surjective)

private theorem odd_two_extension_three_free (N : Subgroup E) [N.Normal]
    {d : ℕ} (hd : d.Prime) (hd3 : 3 < d) (hN : IsPGroup d N)
    (hq : IsPGroup 2 (E ⧸ N)) : Nat.Coprime 3 (Nat.card E) := by
  let : Fact d.Prime := ⟨hd⟩
  obtain ⟨n,hn⟩ := hN.exists_card_eq
  obtain ⟨m,hm⟩ := hq.exists_card_eq
  have h3d : Nat.Coprime 3 d := (Nat.coprime_primes Nat.prime_three hd).mpr (by omega)
  rw [← N.card_mul_index,N.index_eq_card,hn,hm]
  exact (h3d.pow_right n).mul_right ((by decide : Nat.Coprime 3 2).pow_right m)

/-- B.5.6 excludes the odd-prime branch on the actual constituent image.
All FF and rank-loss inequalities are derived from the ambient actor bound. -/
theorem copies_exclude_odd (hAE : A ≤ E) (hA : IsElementaryTwo A)
    (U W : Subrepresentation (ρ.comp E.subtype))
    (τ : Representation (ZMod 2) E I) (hi : IsIrreducible τ)
    {r j : ℕ} (hr : 1 < r) (hj : j ≤ 1)
    (e : (W.toSubmodule ⧸ (sectionLower (ρ.comp E.subtype) U W).toSubmodule) ≃ₗ[ZMod 2]
      (Fin r → I))
    (he : ∀ g v, e (sectionRepresentation (ρ.comp E.subtype) U W g v) =
      fun i => τ g (e v i))
    (hb : fixedCodim ρ A ≤ j + rank A)
    (hne : actor ρ E A U W ≠ ⊥) (hA2 : rank A ≤ 2)
    (c : SQTKQuotient KnownSimple.IsKnownSimple E)
    (N : Subgroup E) [N.Normal] {d : ℕ} (hd : d.Prime) (hd3 : 3 < d)
    (hN : IsPGroup d N) (hq : IsPGroup 2 (E ⧸ N)) : False := by
  have hoff := copies_offender hAE hA U W τ hr hj e he hb hne
    (epsilon_le_one hAE hA U W hne hA2)
  have hthree := (odd_two_extension_three_free N hd hd3 hN hq).coprime_dvd_right
    (Subgroup.card_dvd_of_surjective (actionHom τ) τ.asGroupHom.rangeRestrict_surjective)
  exact ChapterB.SourceInduction.no_ff_of_three_free (imageRepresentation_injective τ)
    (actionImage_twoCore_eq_bot τ hi) (imageCover c τ) hthree
    ⟨actionSubgroup τ (A.subgroupOf E),hoff⟩
/-- The still-to-be-constructed odd branch of the chief-section argument.
Every field is structural data on the literal candidate action: the actor,
its section and repeated constituent, and an odd-prime-by-two acting group.
There is no FF inequality or classification conclusion among the fields. -/
structure Data (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) where
  overgroup : Subgroup (Q)
  actor_le : A ≤ overgroup
  actor_rank : rank (A) ≤ 2
  lower : Subrepresentation ((ρ).comp overgroup.subtype)
  upper : Subrepresentation ((ρ).comp overgroup.subtype)
  lower_le_upper : lower ≤ upper
  Space : Type u
  [spaceAdd : AddCommGroup Space]
  [spaceModule : Module (ZMod 2) Space]
  [spaceFinite : FiniteDimensional (ZMod 2) Space]
  representation : Representation (ZMod 2) overgroup Space
  irreducible : IsIrreducible representation
  multiplicity : ℕ
  multiple : 1 < multiplicity
  coordinates : (upper.toSubmodule ⧸
    (sectionLower ((ρ).comp overgroup.subtype) lower upper).toSubmodule) ≃ₗ[ZMod 2]
      (Fin multiplicity → Space)
  intertwines : ∀ g v, coordinates
    (sectionRepresentation ((ρ).comp overgroup.subtype) lower upper g v) =
      fun i => representation g (coordinates v i)
  moves : RepeatedSectionBudget.actor (ρ) overgroup (A) lower upper ≠ ⊥
  oddSubgroup : Subgroup overgroup
  [oddNormal : oddSubgroup.Normal]
  prime : ℕ
  prime_prime : prime.Prime
  prime_gt_three : 3 < prime
  odd_group : IsPGroup prime oddSubgroup
  two_quotient : IsPGroup 2 (overgroup ⧸ oddSubgroup)

attribute [instance] Data.spaceAdd Data.spaceModule
  Data.spaceFinite Data.oddNormal

/-- Eliminate a marked repeated section using the computed FF inequality. -/
theorem Data.impossible {j : ℕ} (hj : j ≤ 1) (hA : IsElementaryTwo A)
    (hb : fixedCodim ρ A ≤ j + rank A)
    (c : SQTKQuotient KnownSimple.IsKnownSimple Q) (d : Data ρ A) : False :=
  copies_exclude_odd d.actor_le hA d.lower d.upper d.representation d.irreducible
    d.multiple hj d.coordinates d.intertwines hb d.moves d.actor_rank
    (c.subgroup d.overgroup) d.oddSubgroup d.prime_prime d.prime_gt_three d.odd_group d.two_quotient

end OddSection

open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

private theorem sqtk_of_le {B C : Subgroup G} (hBC : B ≤ C)
    (hC : IsSQTK KnownSimple.IsKnownSimple C) : IsSQTK KnownSimple.IsKnownSimple B :=
  (IsSQTK.equiv (subgroupOfEquivOfLe hBC)).mp (hC.subgroup (B.subgroupOf C))

private def literalHatCover (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hsq : IsSQTK KnownSimple.IsKnownSimple (commonGroup T L Y j)) :
    SQTKQuotient KnownSimple.IsKnownSimple (HatGroup T L Y j) where
  Cover := commonGroup T L Y j
  kernel := centralizer (commonModule T L Y j : Set (commonGroup T L Y j))
  sqtk := hsq
  equiv := MulEquiv.refl _

/-- The literal common group stays inside the original candidate two-local. -/
theorem commonGroup_le_candidate {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ) :
    commonGroup T L Y j ≤ H := by
  unfold commonGroup
  apply sup_le hAH
  apply sup_le
  · exact (thompson_commutator_invariance w hTH hAH hTL j).1.trans w.witness.le_overgroup
  · exact (radicalSylowCentralizer_le T L).trans hTH

private theorem literalSQTK (T L Y H : Subgroup G) (j : ℕ)
    (hBH : commonGroup T L Y j ≤ H) (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (commonGroup T L Y j) :=
  @sqtk_of_le G _ _ (commonGroup T L Y j) H hBH hH

private theorem localSQTK (h : Hypothesis1311 T) (H : Subgroup G)
    (hH : IsMaximalTwoLocal H) : IsSQTK KnownSimple.IsKnownSimple H :=
  h.simpleQTKE.twoLocal_sqtk hH.1

/-- SQTK inheritance uses containment in the original candidate, before
passing to its centralizer quotient. -/
theorem commonGroup_sqtk (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ) :
    IsSQTK KnownSimple.IsKnownSimple (commonGroup T L Y j) := by
  exact literalSQTK (T : Subgroup G) L Y H j
    (commonGroup_le_candidate w hTH hAH hTL j) (localSQTK h H hH)

/-- The original two-local supplies a literal SQTK cover of the hat group.
No claim that a centralizer quotient is itself SQTK is needed. -/
def common_hat_cover (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (j : ℕ) [(commonModule T L Y j).Normal] :
    SQTKQuotient KnownSimple.IsKnownSimple (HatGroup T L Y j) :=
  literalHatCover (T : Subgroup G) L Y j (commonGroup_sqtk h w hH hTH hAH hTL j)

/-- Specialization of the marked odd section to the literal hat action. -/
abbrev OddRepeatedSection (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)] :=
  OddSection.Data (hatRepresentation T L Y j) (hatImage T L Y j A)

/-- On the literal candidate quotient, a repeated chief-section constituent
cannot have an odd-prime-by-two actor for a prime greater than three. -/
theorem common_action_excludes_odd_section (h : Hypothesis1311 T) {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {j : ℕ} [(commonModule T L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j) (hj : j ≤ 1)
    (hA : A ∈ ChapterB.thompsonFamily (radicalSylowCentralizer T L) j)
    (hAn : hatImage T L Y j A ≠ ⊥)
    (d : OddRepeatedSection (T : Subgroup G) L Y A j) : False := by
  have hb := ha.actor_bound A hA hAn
  exact d.impossible hj hb.1 hb.2 (common_hat_cover h w hH hTH hAH hTL j)

/-- The actual candidate application excludes every odd repeated section;
constructing the common section remains with this task's final assembly. -/
theorem candidate_excludes_odd_repeated_section (h : Hypothesis1311 T)
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
            hatImage T L Y j A ≠ ⊥ → IsEmpty (OddRepeatedSection (T : Subgroup G) L Y A j) := by
  obtain ⟨Y,w,hm,n,he⟩ := candidate_common_action_with_actor_alternative h hmany hs hrig hclass
    hL hn hH hTH hne hC hAC hN
  let := n
  obtain ⟨e,ha,hactor⟩ := he
  let := e
  refine ⟨Y,w,hm,n,e,ha,hactor,?_⟩
  intro A hA hAn
  refine ⟨fun d => ?_⟩
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  exact common_action_excludes_odd_section h w hH hTH (hAC.trans hC.1) hTL ha hj hA hAn d

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
