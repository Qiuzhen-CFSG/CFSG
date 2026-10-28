module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportDisplacement
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportActorRank

/-!
# Actor rank and field comparison on the literal normalizer orbit

Retain N = C_A(K) ∩ C_A(X) while restricting to the two original natural
SL₃ coordinates. Their rank bounds give rank(A) ≤ rank(N) + 2(m+n), and
the checked displacement cost gives 2n ≤ m + 2 rank(N).

If N is nontrivial, generalized-Fitting detection and D.2.13 produce a
further component distinct from X. The literal centralizer has three-rank
one, so that component is three-free. The existing source recognition and
normalized-support exclusion identify an actual exchanged Suzuki pair.
Consequently every original starred actor gives such a pair or a normal
natural support with rank(A) ≤ 2(m+n) and 2n ≤ m. No triviality of the
simultaneous centralizer or containment of A in KX is assumed.

The remaining complementary displacement estimate, Suzuki exclusion, other
FF branches, U = W and Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.15--19 and the final D.3.10 argument,
printed pp.202--204, applied in3.2.5, p.580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The two natural coordinates account for all but the simultaneous
centralizer. A nontrivial remainder moves an additional exchanged Suzuki pair. -/
theorem normalizer_normal_support_actor_rank_or_suzuki
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    let P := S ⊓ subspaceStabilizer ρ I
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∀ X : Subgroup (internalActionImage M U hn),
        X.Normal → IsQuasisimple X → X ≤ C → ⁅X,A ⊓ C⁆ = X → primeRank 3 X = 1 →
        let N := (A ⊓ C) ⊓ centralizer (X : Set (internalActionImage M U hn))
        ∃ (R : Submodule (ZMod 2) (Additive U)) (hR : IsIrrPlusWith ρ X P R)
          (F₁ : BinaryField), Odd F₁.degree ∧ R ≤ I ∧ P ≤ subspaceStabilizer ρ R ∧
          Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
            (linearNatural F₁ 3)) ∧
          6 * F₁.degree + 3 * F.degree ≤ 2 * rank A ∧
          rank A ≤ rank N + 2 * (F.degree + F₁.degree) ∧
          2 * F₁.degree ≤ F.degree + 2 * rank N ∧
          ((N = ⊥ ∧ 2 * F₁.degree ≤ F.degree) ∨
            (N ≠ ⊥ ∧ ∃ J : Subgroup (internalActionImage M U hn),
              IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ J ≠ X ∧
              ¬ 3 ∣ Nat.card J ∧ ⁅componentOrbit J A,N⁆ = componentOrbit J A ∧
              (componentOrbit J A).Normal ∧
              ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
                ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
                  (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
                  componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA X hXN hqs hXC hXB hr N
  let := hXN
  let := hqs
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  obtain ⟨_,_,_,R,hR,F₁,ho₁,hRI,⟨a⟩,_,hcost⟩ :=
    D.normalizer_normal_support_movement_and_cost h hmany hc hm hne F ho e
      A hAS hA X hXN hqs hXC hXB hr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hinner⟩ :=
    D.normalizer_normal_support_strong_linearThree h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB hr
  have hPR := homogeneous_support_invariant_of_inner ρ hR hinner
  have hAP : A ≤ P := le_inf hAS
    (D.normalizer_starred_stabilizes_isotypic_of_moved_of_many h hmany hc hm hne A hAS hA)
  let B := A ⊓ C
  let := hA.1.2.1.2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (inclusion (show B ≤ A from inf_le_left)) (inclusion_injective _)
  have hrB := natural_support_actor_rank ρ X B R hR.isIrrPlus F₁ ho₁ a
    ((show B ≤ A from inf_le_left).trans (hAP.trans hPR)) inferInstance
  obtain ⟨_,_,_,hrA,_⟩ := D.normalizer_starred_inner_and_rank_of_odd_linearThree
    h hmany hc hm hne F ho e A hAS hA
  change rank B ≤ rank N + 2 * F₁.degree at hrB
  change rank A ≤ rank B + 2 * F.degree at hrA
  have hrank : rank A ≤ rank N + 2 * (F.degree + F₁.degree) := by omega
  have hdegree : 2 * F₁.degree ≤ F.degree + 2 * rank N := by omega
  refine ⟨R,hR,F₁,ho₁,hRI,hPR,⟨a⟩,hcost,hrank,hdegree,?_⟩
  by_cases hN : N = ⊥
  · left
    refine ⟨hN,?_⟩
    simpa only [hN,BinaryOffender.rank_bot,mul_zero,add_zero] using hdegree
  · right
    refine ⟨hN,?_⟩
    have hX : IsComponent (internalActionImage M U hn) X :=
      ⟨hXN.isSubnormal,hqs⟩
    have h3 : 3 ∣ Nat.card X := by
      by_contra hnot
      have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot
      rw [hr] at hz
      omega
    obtain ⟨J,hJ,hJC,hJX,hJ3,hJN⟩ := common_centralizer_moves_three_free_component
      ρ (UniqueFactor.imageRepresentation_injective M U hn) K X A N
      (D.normalizerActor_twoCore_eq_bot h.toHypothesis1221)
      (D.normalizer_component_fully_moved h.toHypothesis1221 hc) hX hXC
      (D.normalizer_component_centralizer_three_rank_bound_of_many h hmany hc hm) h3 hA
      (inf_le_left.trans inf_le_left) hN (inf_le_left.trans inf_le_right) inf_le_right
    have hJB : ⁅componentOrbit J A,A ⊓ C⁆ = componentOrbit J A := by
      apply le_antisymm
        (le_normalizer_iff_commutator_le_left.mp
          (inf_le_left.trans (le_normalizer_componentOrbit J A)))
      calc
        componentOrbit J A = ⁅componentOrbit J A,N⁆ := hJN.symm
        _ ≤ ⁅componentOrbit J A,A ⊓ C⁆ := commutator_mono le_rfl inf_le_left
    have hmove := D.normalizer_starred_moved_three_free_component_not_normalized
      h hc J A hJ hJC hJ3 hA hJB
    obtain ⟨r,hrpos,ej⟩ := D.normalizer_action_component_suzuki_of_three_free h J hJ hJ3
    obtain ⟨hpair,a,ha,han,hi,he,_⟩ := moved_component_orbit_normal_pair
      (D.normalizer_action_layer_sqtk h).stronglyQuasithin J A hJ hmove
    exact ⟨J,hJ,hJC,hJX,hJ3,hJN,hpair,r,hrpos,ej,a,ha,han,hi,he⟩

/-- On the original enlargement, each starred actor yields an exchanged
Suzuki pair or a normal natural support with the exact rank bound and the
necessary field inequality 2n ≤ m. No simultaneous-centralizer premise remains. -/
theorem normalizer_support_rank_degree_or_suzuki
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    let P := S ⊓ subspaceStabilizer ρ I
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ((∃ J : Subgroup (internalActionImage M U hn),
          IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧
          ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
            ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
              (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
              componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom) ∨
        ∃ X : Subgroup (internalActionImage M U hn),
          X.Normal ∧ IsQuasisimple X ∧ X ≤ C ∧ ⁅X,A ⊓ C⁆ = X ∧ primeRank 3 X = 1 ∧
          ∃ (R : Submodule (ZMod 2) (Additive U)) (hR : IsIrrPlusWith ρ X P R)
            (F₁ : BinaryField), Odd F₁.degree ∧ R ≤ I ∧ P ≤ subspaceStabilizer ρ R ∧
            Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
              (linearNatural F₁ 3)) ∧
            6 * F₁.degree + 3 * F.degree ≤ 2 * rank A ∧
            rank A ≤ 2 * (F.degree + F₁.degree) ∧ 2 * F₁.degree ≤ F.degree) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA
  obtain ⟨X,J,hXN,hXC,_,hXB,hJ,hJC,hX,hcases⟩ :=
    D.normalizer_starred_normal_support_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  rcases hcases with ⟨r,hr,ej,a,ha,han,hi,he,_⟩ | ⟨he,hJN,hr,_⟩
  · exact Or.inl ⟨J,hJ,hJC,r,hr,ej,a,ha,han,hi,hX.symm.trans he⟩
  · have hqs : IsQuasisimple X := he.symm ▸ hJ.2
    have hrX : primeRank 3 X = 1 := he.symm ▸ hr
    obtain ⟨R,hR,F₁,ho₁,hRI,hPR,a,hcost,hrank,_,hcase⟩ :=
      D.normalizer_normal_support_actor_rank_or_suzuki h hmany hc hm hne F ho e
        A hAS hA X hXN hqs hXC hXB hrX
    rcases hcase with ⟨hz,hdeg⟩ | ⟨_,J',hJ',hJC',_,_,_,_,r,hr',ej,a,ha,han,hi,he'⟩
    · right
      refine ⟨X,hXN,hqs,hXC,hXB,hrX,R,hR,F₁,ho₁,hRI,hPR,a,hcost,?_,hdeg⟩
      simpa only [hz,BinaryOffender.rank_bot,zero_add] using hrank
    · exact Or.inl ⟨J',hJ',hJC',r,hr',ej,a,ha,han,hi,he'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
