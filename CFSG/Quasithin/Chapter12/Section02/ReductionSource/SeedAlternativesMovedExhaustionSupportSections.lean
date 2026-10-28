module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionNormalSupport
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportSections

/-!
# Selected sections for the literal normal support

Every starred actor in the remaining odd-degree natural SL₃ branch has
normal component-orbit support in C(Aut_L(U)). On the original isotypic
pair the support forces strict ratio decrease on both halves. A homogeneous
Irr⁺ member is selected inside the first half for its actual Sylow
stabilizer, and its exchanged copy is disjoint. The literal component image
moves this selected member. Its component orbit stays in the same half,
is strictly larger, and is fully moved by the support. This is the literal
U_I used in the final multiplicity argument. Normal quasisimple support gives an FF half
unless the same starred actor has nontrivial centralizer on that support.

No full movement or vanishing support-fixed-space hypothesis is added.
The support FF classification, remaining centralizer and multiplicity
exclusions, U = W and Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.17, p.203, applied in3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal normal support supplies a homogeneous section in the first
isotypic half, a disjoint moved Sylow copy, and strict cubic ratios on both
halves. A quasisimple support gives an FF half unless the actor has a
nontrivial centralizer on that same support. -/
theorem normalizer_normal_support_sections
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∀ X J : Subgroup (internalActionImage M U hn),
        X.Normal → X ≤ C → X ≠ ⊥ → ⁅X,A ⊓ C⁆ = X →
        IsComponent (internalActionImage M U hn) J → X = componentOrbit J A →
        ∃ t : M, t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧
          IsCompl I (I.map (ρ (f t))) ∧
          (restrictedSubgroup ρ I A ∈ Qhat (subspaceImageRepresentation ρ I) ∧
            actionRatio (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) < cubicRatio ρ) ∧
          (restrictedSubgroup ρ (I.map (ρ (f t))) A ∈
              Qhat (subspaceImageRepresentation ρ (I.map (ρ (f t)))) ∧
            actionRatio (subspaceImageRepresentation ρ (I.map (ρ (f t))))
              (restrictedSubgroup ρ (I.map (ρ (f t))) A) < cubicRatio ρ) ∧
          (IsQuasisimple X → A ⊓ centralizer (X : Set _) ≠ ⊥ ∨
            IsFFModule (subspaceImageRepresentation ρ I)) ∧
          ∃ R : Submodule (ZMod 2) (Additive U), R ≤ I ∧
            IsIrrPlusWith ρ X (S ⊓ subspaceStabilizer ρ I) R ∧
            IsIrrPlus ρ X (R.map (ρ (f t))) ∧
            Disjoint R (R.map (ρ (f t))) ∧ R.map (ρ (f t)) ≠ R ∧
            R < orbitSpan ρ S R ∧ ¬ K ≤ subspaceStabilizer ρ R ∧
            R < orbitSpan ρ K R ∧ orbitSpan ρ K R ≤ I ∧
            X ≤ subspaceStabilizer ρ (orbitSpan ρ K R) ∧
            subspaceCommutator ρ (orbitSpan ρ K R) X = orbitSpan ρ K R ∧
            ¬ IsIrrPlus ρ X (orbitSpan ρ K R) := by
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
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  dsimp only
  intro A hAS hA X J hXN hXC hXn hXB hJ hX
  let := hXN
  let : Group.IsPerfect X := hX ▸ hJ.orbit_isPerfect A
  obtain ⟨t,ht,hnt,hcompl,hAI,hAIt,hXI,hXIt,hIm,hItm,_,_,_⟩ :=
    D.normalizer_normal_support_on_isotypic_pair h hmany hc hm hne
      A hAS hA X J hXN hXC hXn hJ hX
  have hrat := support_pair_strict_ratios ρ X A (A ⊓ C) hA inf_le_left hXB
    I (I.map (ρ (f t))) hcompl.disjoint hXI hXIt hAI hAIt hIm hItm
  have htS : f t ∈ S := by
    exact mem_map_of_mem f (show t ∈ (T : Subgroup G).subgroupOf M from ht)
  have hseed := exists_homogeneous_support_seed_in_half ρ X K S
    (internalSylow T M U hn D.sylow_normalizes_component).isPGroup'
    (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    (le_centralizer_iff.mp hXC) I hXI hIm (f t) htS hcompl.disjoint
  obtain ⟨R,hRI,hR,hRt,hd,hnR,horbit,hKR⟩ := hseed
  have hKI : K ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    rintro k ⟨l,hl,rfl⟩ v hv
    exact (typePart (internalSubrepresentation hn D.normalizes)).apply_mem_toSubmodule ⟨l,hl⟩ hv
  have hKRorbit := support_seed_commuting_orbit ρ X K
    (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    (le_centralizer_iff.mp hXC) I R hKI hRI hR.isIrrPlus
  refine ⟨t,ht,hnt,hcompl,hrat.1,hrat.2,?_,R,hRI,hR,hRt,hd,hnR,horbit,hKR,hKRorbit⟩
  intro hqs
  let := hqs
  exact quasisimple_support_half_ff_or_centralizer ρ X A hA.1.2.1
    ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1))
    I (f t) hcompl.disjoint hXI hXIt hAI hAIt hIm hItm

/-- In the remaining odd-degree natural SL₃ case, every original starred
actor has an actual normal support and the selected section of D.3.17.
All selection, movement and strict-ratio premises come from the chosen seed. -/
theorem normalizer_starred_support_sections_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map f
    let C := centralizer (K : Set (internalActionImage M U hn))
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∃ X J : Subgroup (internalActionImage M U hn),
        X.Normal ∧ X ≤ C ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        IsComponent (internalActionImage M U hn) J ∧ X = componentOrbit J A ∧
        (restrictedSubgroup ρ I A ∈ Qhat (subspaceImageRepresentation ρ I) ∧
          actionRatio (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) < cubicRatio ρ) ∧
        (IsQuasisimple X → A ⊓ centralizer (X : Set _) ≠ ⊥ ∨
          IsFFModule (subspaceImageRepresentation ρ I)) ∧
        ∃ (t : M) (R : Submodule (ZMod 2) (Additive U)),
          t.val ∈ (T : Subgroup G) ∧ t.val ∉ normalizer (V : Set G) ∧ R ≤ I ∧
          IsIrrPlusWith ρ X (S ⊓ subspaceStabilizer ρ I) R ∧
          IsIrrPlus ρ X (R.map (ρ (f t))) ∧
          Disjoint R (R.map (ρ (f t))) ∧ R.map (ρ (f t)) ≠ R ∧
          R < orbitSpan ρ S R ∧ ¬ K ≤ subspaceStabilizer ρ R ∧
            R < orbitSpan ρ K R ∧ orbitSpan ρ K R ≤ I ∧
            X ≤ subspaceStabilizer ρ (orbitSpan ρ K R) ∧
            subspaceCommutator ρ (orbitSpan ρ K R) X = orbitSpan ρ K R ∧
            ¬ IsIrrPlus ρ X (orbitSpan ρ K R) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro A hAS hA
  obtain ⟨X,J,hXN,hXC,hXn,hXB,hJ,_,hX,_⟩ :=
    D.normalizer_starred_normal_support_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  obtain ⟨t,ht,hnt,_,hr,_,hff,R,hRI,hR,hRt,hd,hnR,horbit,hKR,hKRorbit⟩ :=
    D.normalizer_normal_support_sections h hmany hc hm hne A hAS hA X J hXN hXC hXn hXB hJ hX
  exact ⟨X,J,hXN,hXC,hXn,hXB,hJ,hX,hr,hff,t,R,ht,hnt,hRI,hR,hRt,hd,hnR,horbit,hKR,hKRorbit⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
