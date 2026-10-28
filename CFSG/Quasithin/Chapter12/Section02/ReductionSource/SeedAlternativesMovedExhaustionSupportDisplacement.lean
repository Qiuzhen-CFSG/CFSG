module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportMultiplicity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionStrictCost
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportDisplacement

/-!
# Starred movement and support displacement on the chosen normalizer orbit

The original normal-support branch supplies the stable natural seed and its
commuting-component orbit. Its three-copy lower bound forces the starred
actor to move the chosen component. Thus the local D.3.19 cost is exactly
3m, with no movement premise. The actual subactor B = C_A(K) costs at least
6n across the two support orbits, giving 6n + 3m ≤ 2 rank(A).

The remaining reverse field-degree bound, Suzuki-pair exclusion, U = W and
Source325 assembly remain with qt-baumann-fsu. Every action and centralizer
below is taken in the literal chosen normalizer image.
Source: Aschbacher--Smith D.3.18--19 and the final D.3.10 argument,
printed pp.203--204, applied in3.2.5, p.580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- D.3.18 and the support side of the final displacement budget, with the
component movement premise discharged on the original normal-support branch. -/
theorem normalizer_normal_support_movement_and_cost
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
    let W := internalSection U (componentOrbit V (T : Subgroup G))
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∀ X : Subgroup (internalActionImage M U hn),
        X.Normal → IsQuasisimple X → X ≤ C → ⁅X,A ⊓ C⁆ = X → primeRank 3 X = 1 →
        ¬ A ≤ C ∧ ⁅K,A⁆ = K ∧
        fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) = 3 * F.degree ∧
        ∃ (R : Submodule (ZMod 2) (Additive U)) (hR : IsIrrPlusWith ρ X P R)
          (F₁ : BinaryField), Odd F₁.degree ∧ R ≤ I ∧
          Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
            (linearNatural F₁ 3)) ∧
          6 * F₁.degree ≤ fixedCodim ρ (A ⊓ C) ∧
          6 * F₁.degree + 3 * F.degree ≤ 2 * rank A := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P W A hAS hA X hXN hqs hXC hXB hr
  let := hXN
  let := hqs
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  obtain ⟨_,R,_,_,hRI,hR,_,hnatural,hstrong,hmodel,_⟩ :=
    D.normalizer_normal_support_strong_linearThree h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB hr
  obtain ⟨_,hi,F₁,ho₁,⟨a⟩⟩ := support_seed_marked_natural
    ρ X P (D.normalizerActor_twoCore_eq_bot h.toHypothesis1221) R hR
    hnatural.2.1 hstrong hmodel
  have hKI : K ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    rintro k ⟨l,hl,rfl⟩ v hv
    exact (typePart (internalSubrepresentation hn D.normalizes)).apply_mem_toSubmodule ⟨l,hl⟩ hv
  obtain ⟨hlt,hOI,_,_,_⟩ := support_seed_commuting_orbit ρ X K
    (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    (le_centralizer_iff.mp hXC) I R hKI hRI hR.isIrrPlus
  obtain ⟨a₀,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221
    (Or.inl ⟨F,⟨e⟩⟩)
  have hd := support_commuting_linearThree_triple_degree ρ X K
    (le_centralizer_iff.mp hXC)
    (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    F ho (a₀.groupEquiv.trans e.groupEquiv) R hR.isIrrPlus hi hlt
  obtain ⟨t,ht,_,hcompl,_,_,hperm,_⟩ :=
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
  have hS := (internalSylow T M U hn D.sylow_normalizes_component).isPGroup'
  have hmove := normal_support_starred_not_centralizing ρ X K S P A hS inf_le_left hSP hAP hA
    hXB R I hR hnatural.2.1 F₁ ho₁ a hi hd hOI (f t) htS hcompl.disjoint
  have hcost := D.normalizer_starred_local_cost_of_odd_linearThree h hmany hc hm hne
    F ho e A hAS hA hmove
  let B := A ⊓ C
  have hBP : B ≤ P := inf_le_left.trans hAP
  have hB := hS.to_le (hBP.trans inf_le_left)
  have hlower := support_pair_six_degree_displacement ρ X K P B R I hR.isIrrPlus
    hnatural.2.2.1 hBP hB inf_le_right hXB F₁ ho₁ a hi hd hOI (f t) (hSP htS) hcompl.disjoint
  let O := orbitSpan ρ K R
  let Y := O ⊔ O.map (ρ (f t))
  have hupper := fixedCodim_kernel_add_restricted_le ρ Y B hlower.1
  have h6 : 6 * F₁.degree ≤ fixedCodim ρ B := by
    have hh := hlower.2
    change 6 * F₁.degree ≤ fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y B) at hh
    omega
  have hcomm : ⁅K,A⁆ = K :=
    (show IsComponent (internalActionImage M U hn) K from
      ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩).commutator_eq_self_of_normalizes
      (by rw [normalizer_eq_top]; exact le_top)
      (fun hz => hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)))
  have hsum : 6 * F₁.degree + 3 * F.degree ≤ 2 * rank A := by
    have hh := hcost.2.2
    change fixedCodim ρ B + 3 * F.degree ≤ 2 * rank A at hh
    omega
  exact ⟨hmove,hcomm,hcost.1,R,hR,F₁,ho₁,hRI,⟨a⟩,h6,hsum⟩


/-- Every original starred actor yields the retained exchanged Suzuki pair or
the normal-support movement and displacement conclusions on its original action.
The normal-support premises are discharged by the existing support theorem. -/
theorem normalizer_support_movement_cost_or_suzuki
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
    let W := internalSection U (componentOrbit V (T : Subgroup G))
    ∀ A : Subgroup (internalActionImage M U hn), A ≤ S → A ∈ QhatStar ρ →
      ∃ X J : Subgroup (internalActionImage M U hn),
        X.Normal ∧ X ≤ C ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
        IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
        ((∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
            ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
              (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
              X = J ⊔ J.map (MulAut.conj a).toMonoidHom) ∨
          (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥ ∧
            ¬ A ≤ C ∧ ⁅K,A⁆ = K ∧
            fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) = 3 * F.degree ∧
            ∃ (R : Submodule (ZMod 2) (Additive U)) (hR : IsIrrPlusWith ρ X P R)
              (F₁ : BinaryField), Odd F₁.degree ∧ R ≤ I ∧
              Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
                (linearNatural F₁ 3)) ∧
              6 * F₁.degree ≤ fixedCodim ρ (A ⊓ C) ∧
              6 * F₁.degree + 3 * F.degree ≤ 2 * rank A)) := by
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
    exact Or.inr ⟨he,hJN,hr,hcore,
      D.normalizer_normal_support_movement_and_cost h hmany hc hm hne F ho e
        A hAS hA X hXN hqs hXC hXB hrX⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
