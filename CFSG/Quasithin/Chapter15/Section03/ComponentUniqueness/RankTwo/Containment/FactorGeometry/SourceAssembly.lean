module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.CenterComparison.OrbitEquality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.ThreePart
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.FactorIdentification
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Source assembly of the factor geometry in 15.3.39--40

In a strict orbit the source model comparison makes the two conjugate
components simple. Their direct product makes the action on L inner.
The splitting and order clauses of 15.3.12(2) then give the two conjugate
residual factors, a simple quotient by a normal two-subgroup of each
factor, and the order-nine quotient of Y₊. Only now is the natural-action construction applied to
produce the two plane actors. The swapped-product projection argument
contradicts their commutator identities and proves L = ⟨L^S⟩.

In the single-component branch, the corrected rank-one splitting gives
the quotient used to construct the actors. The quotient by O₂,Φ(Y₊S)
identifies them with the component and centralizing residuals. Applying
the plane-interchange theorem then orients a definite plane inside L.
The remaining model restrictions and contradiction of 15.3.40 belong
to the containment assembly, not to this factor-geometry implication.

The earlier source inputs are explicit: 15.3.7's residual image,
15.3.11's Sylow conclusion and rank-two case, the relevant clauses of
15.3.12(2), 15.3.33(3), the positive-rank clause of 15.3.34, the weak
orbit consequence of corrected 15.3.37, the local SQTK bound, and the
complete nonnormal alternative of 1.2.1(3). No actor, projection,
centerlessness, or source containment is an additional premise.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.39--40, printed pp.1137--1138; earlier inputs on pp.1121--1125 and
1134--1135. The three-part correction is recorded in
`docs/quasithin-proof-basis.md`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The actual two simple components and conjugate residual factors under
strict orbit containment. The normal two-subgroup of X is constructed by
mapping X to Y₊/O₂(Y₊); neither a projection nor a quotient witness is assumed. -/
theorem strict_componentOrbit_factors_of_source_inputs
    {M Yplus L I S : Subgroup G} {z : G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I))
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) M z)
    (hSQT : IsStronglyQuasithin I) (h34 : 1 ≤ primeRank 3 L)
    (h121 : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel
          ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (hSY : S ≤ normalizer (Yplus : Set G))
    (h37 : L ≠ componentOrbit L S → Yplus ≤ componentOrbit L S)
    (h12 : primeRank 3 L = 1 →
      ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L →
      Yplus = ComponentIntersection.intersectionResidual Yplus L ⊔
        ComponentIntersection.centralizerResidual Yplus L ∧
      3 ^ (Nat.card (componentFactor Yplus L)).factorization 3 = 3 ∧
      Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (hlt : L < componentOrbit L S) :
    Nat.card (Yplus ⧸ pCore 2 Yplus) = 9 ∧
      ∃ s : S, L.map (MulAut.conj (s : G)).toMonoidHom ≠ L ∧
        componentOrbit L S = L ⊔ L.map (MulAut.conj (s : G)).toMonoidHom ∧
        (L.map (MulAut.conj (s : G)).toMonoidHom).map
          (MulAut.conj (s : G)).toMonoidHom = L ∧
        IsSimpleGroup L ∧ IsSimpleGroup (L.map (MulAut.conj (s : G)).toMonoidHom) ∧
        Disjoint L (L.map (MulAut.conj (s : G)).toMonoidHom) ∧
        L ≤ centralizer (L.map (MulAut.conj (s : G)).toMonoidHom : Set G) ∧
        Yplus = componentFactor Yplus L ⊔
          (componentFactor Yplus L).map (MulAut.conj (s : G)).toMonoidHom ∧
        ∃ (Q : Subgroup (componentFactor Yplus L)) (hQn : Q.Normal),
          letI := hQn; IsPGroup 2 Q ∧ IsSimpleGroup ((componentFactor Yplus L) ⧸ Q) := by
  have hSI : S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  obtain ⟨hZ, hrank⟩ :=
    centerless_comparison_of_source_inputs hLI P hP hL h33 hSQT h34 hlt
  have hindex := (nonnormal_model_of_strict_componentOrbit hLI P hP h121 hlt).1.le
  obtain ⟨s, hs, hsup, hswap⟩ := exists_swapping_conjugate hlt
    (component_orbit_card_le_two hLI hSI hindex)
  obtain ⟨hd, hc⟩ := relative_component_conjugate_disjoint_commuting hLI hL hZ
    (⟨s, hSI s.property⟩ : I) hs
  obtain ⟨hsimple, hsimple'⟩ := relative_component_conjugates_simple hLI hL hZ (s : G)
  have hY := (h37 hlt.ne).trans hsup.le
  obtain ⟨hsplit, hthree, hquot⟩ :=
    h12 hrank (inner_on_twoCoreQuotient_of_component_product hd hc hY)
  let := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI)
  have hcent : ComponentIntersection.centralizerResidual Yplus L =
      centralizingFactor Yplus L :=
    sectionCentralizingPart_eq_centralizingPart (IsQuasisimple.pCore_le_center 2)
  change Yplus = componentFactor Yplus L ⊔ ComponentIntersection.centralizerResidual Yplus L at hsplit
  rw [hcent] at hsplit
  exact ⟨hquot, s, hs, hsup, hswap, hsimple, hsimple', hd, hc,
    conjugate_residual_factorization (s : G) hd hc hZ hY (hSY s.property) hsplit,
    exists_componentFactor_simple_quotient Yplus L hthree hquot⟩

/-- Conditional source implication 15.3.39, with all factor geometry
constructed. The actual order-nine quotient is deduced in the strict branch
before constructing the plane actors. The weak 15.3.37 consequence is enough;
the impossible printed full-order clause is not used. -/
theorem componentOrbit_eq_of_source_inputs
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G} {z : G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hL : IsComponent I (L.subgroupOf I))
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z)
    (hSQT : IsStronglyQuasithin I) (h34 : 1 ≤ primeRank 3 L)
    (h121 : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel
          ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h36 : OutsideStructure.RankTwoCase d I)
    (h37 : L ≠ componentOrbit L d.S → d.Yplus ≤ componentOrbit L d.S)
    (h12 : primeRank 3 L = 1 →
      ComponentIntersection.InducesInnerOnTwoCoreQuotient d.Yplus L →
      d.Yplus = ComponentIntersection.intersectionResidual d.Yplus L ⊔
        ComponentIntersection.centralizerResidual d.Yplus L ∧
      3 ^ (Nat.card (componentFactor d.Yplus L)).factorization 3 = 3 ∧
      Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9) :
    L = componentOrbit L d.S := by
  classical
  by_cases heq : L = componentOrbit L d.S
  · exact heq
  have hlt := lt_of_le_of_ne (le_componentOrbit L d.S) heq
  obtain ⟨hSY, hSV₂, hYV₂, hVS, hV₂ne⟩ := source_orbit_plane_facts
    d.action d.T d.sylow_le (localModule_le d.T d.sylow_le)
    1 (Multiplicative.ofAdd (1 : ZMod 2)) d.choice
  have hquot := (strict_componentOrbit_factors_of_source_inputs
    hLI P hP hL h33 hSQT h34 h121 hSY h37 h12 hlt).1
  obtain ⟨actors⟩ := source_planeActorPair_of_rankTwoCase d I h7 h36 hquot
  exact componentOrbit_eq_of_source_comparison_of_planeActors
    hLI P hP hL h33 hSQT h34 h121 hSY hSV₂ hYV₂ hVS hV₂ne
    (Or.inl (h37 heq)) h12 actors

/-- Apply 15.3.39 to the separately named three-part alternatives. Every
other model, product, orbit and quotient clause of 15.3.37 is retained in
the input. The 15.3.12 input uses its literal set product and an actual
E₉ quotient equivalence. Their producers remain earlier-source obligations. -/
theorem componentOrbit_eq_of_threePartAlternatives
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G} {z : G}
    (hLI : L ≤ I) (h11 : OutsideStructure.Conclusions d I)
    (hL : IsComponent I (L.subgroupOf I))
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z)
    (hSQT : IsStronglyQuasithin I) (h34 : 1 ≤ primeRank 3 L)
    (h121 : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel
          ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h36 : OutsideStructure.RankTwoCase d I)
    (h37 : Candidates.Alternatives15337ThreePart d.Yplus L (componentOrbit L d.S))
    (h12 : primeRank 3 L = 1 →
      ComponentIntersection.InducesInnerOnTwoCoreQuotient d.Yplus L →
      (d.Yplus : Set G) =
        (ComponentIntersection.intersectionResidual d.Yplus L : Set G) *
          (ComponentIntersection.centralizerResidual d.Yplus L : Set G) ∧
      3 ^ (Nat.card (componentFactor d.Yplus L)).factorization 3 = 3 ∧
      Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3))) :
    L = componentOrbit L d.S := by
  obtain ⟨P, hP⟩ := h11.sylow
  apply componentOrbit_eq_of_source_inputs d hLI P hP hL h33 hSQT h34 h121
    h7 h36 h37.le_of_orbit_ne
  intro hr hi
  obtain ⟨hp, ht, ⟨e⟩⟩ := h12 hr hi
  refine ⟨?_, ht, ?_⟩
  · rw [sup_eq_closure_mul, ← hp, closure_eq]
  · rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]

/-- In the single-component branch, the full earlier component alternative
and the actual Sylow realization imply normality inside I. -/
theorem relative_normal_of_source_componentOrbit_eq {L I S : Subgroup G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (h121 : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel
          ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (horbit : L = componentOrbit L S) : (L.subgroupOf I).Normal := by
  rcases h121 with hn | ⟨hi, _⟩
  · exact hn
  · exact relative_normal_of_componentOrbit_eq hLI P hP hi.le horbit

/-- Construct the plane actors, identify both component factors with them,
and apply the plane interchange at the start of 15.3.40. The corrected
rank-one alternative retains its actual model and E₉ quotient. No factor
identification, actor existence, or plane containment is an input. -/
theorem source_identified_and_oriented_planeActors
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G} {z : G}
    (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (h11 : OutsideStructure.Conclusions d I)
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z)
    (h121 : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel
          ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h36 : OutsideStructure.RankTwoCase d I)
    (hsplit : Candidates.RankOneThreePartSplit d.Yplus L (componentOrbit L d.S)) :
    ∃ a : PlaneActorPair d.M d.Y d.Yplus d.S d.V d.V₁ d.V₂,
      ((componentFactor d.Yplus L = a.right ∧
          centralizingFactor d.Yplus L = centralizingFactor d.Yplus d.V₂) ∨
        (componentFactor d.Yplus L = centralizingFactor d.Yplus d.V₂ ∧
          centralizingFactor d.Yplus L = a.right)) ∧
      ((componentFactor d.Yplus L = a.right ∧ d.V₂ ≤ L) ∨
        (d.Yplus = d.Y ∧ componentFactor d.Yplus L = centralizingFactor d.Yplus d.V₂ ∧
          d.V₁ ≤ L)) := by
  obtain ⟨P, hP⟩ := h11.sylow
  let : (L.subgroupOf I).Normal :=
    relative_normal_of_source_componentOrbit_eq hLI P hP h121 hsplit.orbit_eq
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have hS : IsPGroup 2 d.S := hP ▸ P.isPGroup'.map I.subtype
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  have hLM : ¬ L ≤ d.M := by
    simpa only [map_subgroupOf_eq_of_le hLI] using h33.outside
  obtain ⟨hSY, hSV₂, hYV₂, hVS, _⟩ := source_orbit_plane_facts
    d.action d.T d.sylow_le (localModule_le d.T d.sylow_le)
    1 (Multiplicative.ofAdd (1 : ZMod 2)) d.choice
  obtain ⟨e⟩ := hsplit.quotient
  have hquot : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨a⟩ := source_planeActorPair_of_rankTwoCase d I h7 h36 hquot
  have hgen : d.Yplus = componentFactor d.Yplus L ⊔ centralizingFactor d.Yplus L := by
    change d.Yplus = componentPart d.Yplus L ⊔ centralizingPart d.Yplus L
    rw [sup_eq_closure_mul, ← hsplit.product, closure_eq]
  have hpair := identify_component_factors_of_relative_normality a hLI hYI hS
    hsplit.orbit_eq hSY hSV₂ hYV₂ hgen
    hsplit.component_three_part hsplit.centralizer_three_part hquot h36.2.1
  refine ⟨a, hpair, orient_component_plane d.choice ?_ hLI hLM
    ((d.action.plane_le 1).trans (hVS.trans hSI))
    ((d.action.plane_le (Multiplicative.ofAdd (1 : ZMod 2))).trans (hVS.trans hSI))
    a.other_plane a.plane_self hpair⟩
  intro hcase
  exact (h11.second_choice hcase).2.2.1

end CFSG.Quasithin.Chapter15.Section03.RankTwo
