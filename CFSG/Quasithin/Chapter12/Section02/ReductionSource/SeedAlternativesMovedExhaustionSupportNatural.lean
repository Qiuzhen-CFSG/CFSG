module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportClassification
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportNatural

/-!
# Natural constituents of the literal normalizer support

The normal rank-one support inherits the checked B.5.1 classification. Its
actual central covering preserves three-rank, and full movement and absence
of fixed vectors identify the classified moved section with the orbit section.
The selected seed has a marked natural SL2, odd-degree SL3, or alternating-five
central quotient. Its defining homogeneity forces its half-stabilizer orbit
to equal the seed. All actor coordinates use the original projection.

The surviving model exclusions, removal of seed fixed vectors where required,
component movement, ambient multiplicities and Suzuki-pair exclusion, U = W,
and final Source325 assembly remain with qt-baumann-fsu. In particular this
result does not assume or assert that the entire normalizer orbit is exhausted.
Source: Aschbacher--Smith D.3.17, p.203, in the proof of3.2.5, p.580;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original normal rank-one support has a marked natural seed quotient
and stabilizes the seed under its actual Sylow half stabilizer. -/
theorem normalizer_normal_quasisimple_support_natural_constituent
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
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
        ∃ (t : M) (R : Submodule (ZMod 2) (Additive U)),
          t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧ R ≤ I ∧
          ∃ hR : IsIrrPlusWith ρ X P R,
            let σ := orbitSectionRepresentation ρ hR
            ∃ B : Subgroup (internalActionImage M U hn), B ≤ P ∧ IsElementaryAbelian 2 B ∧
              IsOffender (KernelQuotient.action σ)
                ((B.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)) ∧
              IsFFModule (KernelQuotient.action σ) ∧
              SupportSectionClassification ρ hR ∧ SupportNaturalSection ρ hR := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA X hXN hqs hXC hXB hr
  let := hqs
  obtain ⟨t,R,ht,hnt,hRI,hR,B,hBP,hB,hoff,hff,hclass⟩ :=
    D.normalizer_normal_quasisimple_support_classification h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB
  exact ⟨t,R,ht,hnt,hRI,hR,B,hBP,hB,hoff,hff,hclass,
    support_natural_section ρ X P hr R hR hclass⟩

/-- Every original starred actor yields an exchanged Suzuki pair or a
stable support seed with actual natural central-quotient coordinates. -/
theorem normalizer_support_natural_or_suzuki_of_odd_linearThree
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
      ∃ X J : Subgroup (internalActionImage M U hn),
        X.Normal ∧ X ≤ C ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
        ((∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
            ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
              (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
              X = J ⊔ J.map (MulAut.conj a).toMonoidHom) ∨
          (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥ ∧
            ∃ (t : M) (R : Submodule (ZMod 2) (Additive U)),
              t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
              R ≤ I ∧ ∃ hR : IsIrrPlusWith ρ X P R,
                SupportSectionClassification ρ hR ∧ SupportNaturalSection ρ hR)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro A hAS hA
  obtain ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,hcases⟩ :=
    D.normalizer_support_classification_or_suzuki_of_odd_linearThree
      h hmany hc hm hne F ho e A hAS hA
  refine ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,?_⟩
  rcases hcases with hpair | ⟨he,hJN,hr,hcore,t,R,ht,hnt,hRI,hR,hclass⟩
  · exact Or.inl hpair
  · let : IsQuasisimple X := he.symm ▸ hJ.2
    have hrX : primeRank 3 X = 1 := he.symm ▸ hr
    exact Or.inr ⟨he,hJN,hr,hcore,t,R,ht,hnt,hRI,hR,hclass,
      support_natural_section _ X _ hrX R hR hclass⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
