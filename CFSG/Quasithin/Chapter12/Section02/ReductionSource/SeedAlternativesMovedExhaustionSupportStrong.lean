module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportNatural
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportStrong

/-!
# Odd-degree SL₃ support on the literal chosen normalizer action

The checked classification and homogeneity stabilize the selected support
seed. The original fixed-free component and complementary isotypic halves
discharge the strict pair-budget argument, yielding a strong offender on
that seed and its literal central orbit section. B.5.1 now eliminates every
ratio-one row, leaving a marked odd-degree natural SL₃ section.

Every actor, inclusion and central quotient is the original Chapter12 map.
The support inherits a trivial two-core, so the actual central covering map
is proved injective and gives the original support an SL₃ marking.
Its compatibility with the original projection is retained explicitly. Odd
field degree then makes the original half stabilizer act by inner
automorphisms on the support, proving the group and inner-action clauses
of D.3.17 in the normal support branch.
The seed central-extension, full movement, multiplicity and Suzuki-pair
exclusions, U = W and final Source325 remain with qt-baumann-fsu.
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

/-- The actual normal rank-one support has a strong offender on the original
seed and central section; its marked central section is odd-degree natural SL₃. -/
theorem normalizer_normal_support_strong_linearThree
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
            SupportSectionClassification ρ hR ∧ SupportNaturalSection ρ hR ∧
              SupportStrongSection ρ hR ∧ SupportMarkedLinearThreeSection ρ hR ∧
                ChapterB.SourceInduction.ComponentReduction.InducesInner P X := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA X hXN hqs hXC hXB hr
  let := hXN
  let := hqs
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  obtain ⟨_,R,_,_,hRI,hR,_,_,_,_,_,hclass,hnatural⟩ :=
    D.normalizer_normal_quasisimple_support_natural_constituent h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB hr
  obtain ⟨t,ht,hnt,hcompl,_,_,hperm,_⟩ :=
    D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
  change IsCompl I (I.map (ρ (f t))) at hcompl
  change ∀ g, I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ (f t)) at hperm
  have hneq : I ≠ I.map (ρ (f t)) := by
    intro he
    have hz : I = ⊥ := disjoint_self.mp (by simpa only [←he] using hcompl.disjoint)
    exact hR.isIrrPlus.ne_bot ρ (bot_unique (hRI.trans hz.le))
  have hSP : S ≤ normalizer (P : Set _) :=
    permuted_pair_normalizes_half_stabilizer ρ I (f t) hneq hperm S
  have hAP : A ≤ P := le_inf hAS
    (D.normalizer_starred_stabilizes_isotypic_of_moved_of_many h hmany hc hm hne A hAS hA)
  have htS : f t ∈ S := mem_map_of_mem f
    (show t ∈ (T : Subgroup G).subgroupOf M from ht)
  have hKI : K ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    rintro k ⟨l,hl,rfl⟩ v hv
    exact (typePart (internalSubrepresentation hn D.normalizes)).apply_mem_toSubmodule ⟨l,hl⟩ hv
  have hmodel := homogeneous_support_strong_marked_linearThree
    ρ X K S P A (A ⊓ C) (D.normalizerActor_twoCore_eq_bot h.toHypothesis1221) hr
    (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    (le_centralizer_iff.mp hXC)
    (internalSylow T M U hn D.sylow_normalizes_component).isPGroup'
    inf_le_left hSP hAP inf_le_left hXB hA I R hKI hRI hR hclass
    (f t) htS hcompl.disjoint
  exact ⟨t,R,ht,hnt,hRI,hR,hclass,hnatural,hmodel⟩


/-- Every original starred actor yields an exchanged Suzuki pair or a
support seed whose marked central section is odd-degree natural SL₃. -/
theorem normalizer_support_strong_linearThree_or_suzuki
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
                SupportSectionClassification ρ hR ∧ SupportNaturalSection ρ hR ∧
                SupportStrongSection ρ hR ∧ SupportMarkedLinearThreeSection ρ hR ∧
                  ChapterB.SourceInduction.ComponentReduction.InducesInner P X)) := by
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
    obtain ⟨t,R,ht,hnt,hRI,hR,hclass,hnatural,hstrong,hmodel,hinner⟩ :=
      D.normalizer_normal_support_strong_linearThree h hmany hc hm hne
        A hAS hA X hXN hqs hXC hXB hrX
    exact Or.inr ⟨he,hJN,hr,hcore,t,R,ht,hnt,hRI,hR,hclass,hnatural,
      hstrong,hmodel,hinner⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
