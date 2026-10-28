module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSupportFixed
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportMultiplicity

/-!
# Natural support multiplicity for the actual chosen normalizer action

The chosen component's original natural SL₃ marking and zero fixed space
force at least three copies in the commuting-component orbit of the selected
support seed. Its natural support marking gives the literal dimension bound
9n. The existing isotypic pair places a disjoint conjugate of the same degree
in the other half, giving 18n for the original normalizer orbit.

This discharges the lower multiplicity premise in the source D.3.18--19
argument. The remaining starred-actor movement and displacement estimates,
Suzuki exclusion, U = W and Source325 assembly stay with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.18 and D.3.10, printed pp.203--204, applied in
3.2.5, p.580; refs/quasithin.pdf.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the original normal-support branch, the commuting-component orbit
contains at least three natural support copies. The two disjoint isotypic
halves therefore have total dimension at least eighteen times the support
field degree. The component marking is transported from the chosen seed. -/
theorem normalizer_normal_support_triple_multiplicity
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
        ∃ (R : Submodule (ZMod 2) (Additive U)) (hR : IsIrrPlusWith ρ X P R),
          R ≤ I ∧ R ⊓ fixedSpace ρ X = ⊥ ∧
          IsIrreducible (invariantSubspace ρ X R hR.invariant).toRepresentation ∧
          R < orbitSpan ρ K R ∧ orbitSpan ρ K R ≤ I ∧
          3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) ∧
          ∃ F₁ : BinaryField, Odd F₁.degree ∧
            Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
              (linearNatural F₁ 3)) ∧
            9 * F₁.degree ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) ∧
            18 * F₁.degree ≤ Module.finrank (ZMod 2) (Additive U) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn f ρ K C I S P A hAS hA X hXN hqs hXC hXB hr
  let := hXN
  let := hqs
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  obtain ⟨_,R,_,_,hRI,hR,_,hfixed,hirr,hlt,hOI,_,_,_,F₁,ho₁,⟨a⟩⟩ :=
    D.normalizer_normal_support_natural_seed h hmany hc hm hne
      A hAS hA X hXN hqs hXC hXB hr
  obtain ⟨a₀,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221
    (Or.inl ⟨F,⟨e⟩⟩)
  have hd := support_commuting_linearThree_triple_degree ρ X K
    (le_centralizer_iff.mp hXC)
    (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    F ho (a₀.groupEquiv.trans e.groupEquiv) R hR.isIrrPlus hirr hlt
  have hfield : Module.finrank (ZMod 2) F₁.Carrier = F₁.degree := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F₁.Carrier)
    rw [Nat.card_zmod,F₁.card_eq] at hh
    exact (Nat.pow_right_injective (by decide : 1 < 2) hh).symm
  have hdim : Module.finrank (ZMod 2) R = 3 * F₁.degree := by
    have he : Module.finrank (ZMod 2) R =
        Module.finrank (ZMod 2) (Fin 3 → F₁.Carrier) := a.linearEquiv.finrank_eq
    rw [he,Module.finrank_pi_fintype]
    simp [hfield]
  have hd9 : 9 * F₁.degree ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) := by
    calc
      9 * F₁.degree = 3 * Module.finrank (ZMod 2) R := by rw [hdim]; omega
      _ ≤ _ := hd
  obtain ⟨t,_,_,hcompl,_,_,_,_⟩ :=
    D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
  change IsCompl I (I.map (ρ (f t))) at hcompl
  have hdis := hcompl.disjoint.mono hOI (Submodule.map_mono (f := ρ (f t)) hOI)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (orbitSpan ρ K R) ((orbitSpan ρ K R).map (ρ (f t)))
  rw [hdis.eq_bot,finrank_bot,add_zero,finrank_map_action] at hsum
  have hle := (orbitSpan ρ K R ⊔ (orbitSpan ρ K R).map (ρ (f t))).finrank_le
  exact ⟨R,hR,hRI,hfixed,hirr,hlt,hOI,hd,F₁,ho₁,⟨a⟩,hd9,by omega⟩

/-- Every original starred actor yields either the retained exchanged Suzuki
pair or an actual natural support orbit with multiplicity at least three.
The normal-support hypotheses in the numerical application are discharged
by the existing support theorem on this same normalizer action. -/
theorem normalizer_support_triple_multiplicity_or_suzuki
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
            ∃ (R : Submodule (ZMod 2) (Additive U)) (hR : IsIrrPlusWith ρ X P R),
              R ≤ I ∧ R ⊓ fixedSpace ρ X = ⊥ ∧
              IsIrreducible (invariantSubspace ρ X R hR.invariant).toRepresentation ∧
              R < orbitSpan ρ K R ∧ orbitSpan ρ K R ≤ I ∧
              3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) ∧
              ∃ F₁ : BinaryField, Odd F₁.degree ∧
                Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
                  (linearNatural F₁ 3)) ∧
                9 * F₁.degree ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) ∧
                18 * F₁.degree ≤ Module.finrank (ZMod 2) (Additive U))) := by
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
      D.normalizer_normal_support_triple_multiplicity h hmany hc hm hne F ho e
        A hAS hA X hXN hqs hXC hXB hrX⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
