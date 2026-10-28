module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportStrong
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportFixed

/-!
# Natural support seeds in the actual chosen normalizer action

The strong offender and the marked central section constructed on the
original normalizer action remove the selected seed's fixed kernel. This
completes the natural-module clause of D.3.17 in the normal support branch:
the original support acts naturally and irreducibly on the seed itself.
Its orbit under the original component is strictly larger, lies in the
same isotypic half, and is fully moved with zero support-fixed space.

The normal-support/Suzuki alternative retains the actual component orbit,
conjugator, quotient action and original multiple-overgroup hypothesis.
Component movement by the starred actor, the final multiplicity estimates,
Suzuki exclusion, U = W and Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.17--18, p.203, applied in3.2.5, p.580;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The selected seed itself is natural SL₃, and its strictly larger orbit under
the original component is fully moved and has no support-fixed vectors. -/
theorem normalizer_normal_support_natural_seed
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
            ChapterB.SourceInduction.ComponentReduction.InducesInner P X ∧
            R ⊓ fixedSpace ρ X = ⊥ ∧
            IsIrreducible (invariantSubspace ρ X R hR.invariant).toRepresentation ∧
            R < orbitSpan ρ K R ∧ orbitSpan ρ K R ≤ I ∧
            X ≤ subspaceStabilizer ρ (orbitSpan ρ K R) ∧
            subspaceCommutator ρ (orbitSpan ρ K R) X = orbitSpan ρ K R ∧
            orbitSpan ρ K R ⊓ fixedSpace ρ X = ⊥ ∧
            ∃ F : BinaryField, Odd F.degree ∧
              Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
                (linearNatural F 3)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA X hXN hqs hXC hXB hr
  let := hXN
  let := hqs
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  obtain ⟨t,R,ht,hnt,hRI,hR,_,hnatural,hstrong,hmodel,hinner⟩ :=
    D.normalizer_normal_support_strong_linearThree h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB hr
  obtain ⟨hfixed,hirr,F,ho,ha⟩ := support_seed_marked_natural
    ρ X P (D.normalizerActor_twoCore_eq_bot h.toHypothesis1221) R hR
    hnatural.2.1 hstrong hmodel
  have hKI : K ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    rintro k ⟨l,hl,rfl⟩ v hv
    exact (typePart (internalSubrepresentation hn D.normalizes)).apply_mem_toSubmodule ⟨l,hl⟩ hv
  obtain ⟨hlt,hOI,hXO,hmove,_⟩ := support_seed_commuting_orbit
    ρ X K (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    (le_centralizer_iff.mp hXC) I R hKI hRI hR.isIrrPlus
  exact ⟨t,R,ht,hnt,hRI,hR,hinner,hfixed,hirr,hlt,hOI,hXO,hmove,
    support_seed_orbit_fixed_eq_bot ρ X K R hR.isIrrPlus hfixed,F,ho,ha⟩

/-- Every original starred actor yields an exchanged Suzuki pair or a
support seed that is itself odd-degree natural SL₃, with its original
commuting-component orbit fully moved and free of support-fixed vectors. -/
theorem normalizer_support_natural_seed_or_suzuki
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
                ChapterB.SourceInduction.ComponentReduction.InducesInner P X ∧
                R ⊓ fixedSpace ρ X = ⊥ ∧
                IsIrreducible (invariantSubspace ρ X R hR.invariant).toRepresentation ∧
                R < orbitSpan ρ K R ∧ orbitSpan ρ K R ≤ I ∧
                X ≤ subspaceStabilizer ρ (orbitSpan ρ K R) ∧
                subspaceCommutator ρ (orbitSpan ρ K R) X = orbitSpan ρ K R ∧
                orbitSpan ρ K R ⊓ fixedSpace ρ X = ⊥ ∧
                ∃ F : BinaryField, Odd F.degree ∧
                  Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
                    (linearNatural F 3)))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro A hAS hA
  obtain ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,hcases⟩ :=
    D.normalizer_starred_normal_support_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  refine ⟨X,J,hXN,hXC,hXn,hXB,hJ,hJC,hX,?_⟩
  rcases hcases with ⟨r,hr,ej,a,ha,han,hindex,hpair,_⟩ | ⟨he,hJN,hr,hcore⟩
  · exact Or.inl ⟨r,hr,ej,a,ha,han,hindex,hpair⟩
  · let hqs : IsQuasisimple X := he.symm ▸ hJ.2
    have hrX : primeRank 3 X = 1 := he.symm ▸ hr
    obtain ⟨t,R,ht,hnt,hRI,hR,hseed⟩ :=
      D.normalizer_normal_support_natural_seed h hmany hc hm hne
        A hAS hA X hXN hqs hXC hXB hrX
    exact Or.inr ⟨he,hJN,hr,hcore,t,R,ht,hnt,hRI,hR,hseed⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
