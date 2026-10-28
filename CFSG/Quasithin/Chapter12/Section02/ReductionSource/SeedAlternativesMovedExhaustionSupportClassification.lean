module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportOrbitFF
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportClassification
/-!
# The classified support quotient in the chosen normalizer action

The previously constructed offender on the central homogeneous orbit section
supplies FF. The actual component inherits SQTK from the original normalizer.
The support-section theorem proves the two-core and component hypotheses,
restricts to the offender subgroup, and applies full corrected B.5.1.

Every starred actor in the surviving odd-degree SL₃ branch consequently gives
either the actual exchanged Suzuki pair or all six B.5.1 clauses on the normal
support's central orbit quotient. The covering map from the original support
is the same literal quotient projection. No centerlessness, component
faithfulness, or classification conclusion is assumed.

The natural-constituent selection, component movement, multiplicity and
Suzuki exclusions, other FF branches, U = W and final Source325 assembly
remain with qt-baumann-fsu. These quotient classification conclusions alone
do not establish the final source alternatives.
Source: Aschbacher--Smith B.5.1 and D.3.17, printed pp.99--103,203,
in the argument for3.2.5, p.580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The normal support gives an explicit central covering and the complete
B.5.1 conclusion on the literal offender-generated section action. -/
theorem normalizer_normal_quasisimple_support_classification
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
        X.Normal → IsQuasisimple X → X ≤ C → ⁅X,A ⊓ C⁆ = X →
        ∃ (t : M) (R : Submodule (ZMod 2) (Additive U)),
          t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧ R ≤ I ∧
          ∃ hR : IsIrrPlusWith ρ X P R,
            let σ := orbitSectionRepresentation ρ hR
            ∃ B : Subgroup (internalActionImage M U hn), B ≤ P ∧ IsElementaryAbelian 2 B ∧
              IsOffender (KernelQuotient.action σ)
                ((B.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)) ∧
              IsFFModule (KernelQuotient.action σ) ∧
              SupportSectionClassification ρ hR := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA X hXN hqs hXC hXB
  let := hqs
  obtain ⟨t,R,ht,hnt,hRI,hR,B,hBP,hB,hoff,hff⟩ :=
    D.normalizer_normal_quasisimple_support_ff_section h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB
  have hX : IsComponent (internalActionImage M U hn) X := ⟨hXN.isSubnormal,hqs⟩
  have hclass := support_section_classification ρ X P
    ((internalSylow T M U hn D.sylow_normalizes_component).isPGroup'.to_le inf_le_left)
    (D.normalizer_action_component_sqtk h X hX) R hR hff
  exact ⟨t,R,ht,hnt,hRI,hR,B,hBP,hB,hoff,hff,hclass⟩

/-- Every starred actor in the surviving SL₃ branch either exchanges the
actual Suzuki pair or has its normal support classified by full B.5.1 on the
literal central orbit quotient. The original support map is retained. -/
theorem normalizer_support_classification_or_suzuki_of_odd_linearThree
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
                SupportSectionClassification ρ hR)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro A hAS hA
  obtain ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,hcases⟩ :=
    D.normalizer_starred_normal_support_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  refine ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,?_⟩
  rcases hcases with ⟨r,hr,ej,a,ha,han,hindex,hpair,_⟩ | ⟨he,hJN,hr,hcore⟩
  · exact Or.inl ⟨r,hr,ej,a,ha,han,hindex,hpair⟩
  · right
    refine ⟨he,hJN,hr,hcore,?_⟩
    obtain ⟨t,R,ht,hnt,hRI,hR,_,_,_,_,_,hclass⟩ :=
      D.normalizer_normal_quasisimple_support_classification h hmany hc hm hne
        A hAS hA X hXN (he.symm ▸ hJ.2) hXC hXB
    exact ⟨t,R,ht,hnt,hRI,hR,hclass⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
