module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualElimination
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics

/-!
# Assembling the binary L₄(2) and L₅(2) exclusions

The four-dimensional module classification constructs the natural alternatives,
excludes repeated naturals, and contradicts the natural-plus-dual case through
its actual point parabolic and the complete C.1.34 classification. For dimension
five, maximal parabolics over Y₊(S ∩ L) generate L. A parabolic outside M gives a
proper characteristic-two outside overgroup PS; its component has quotient
L₃(2) or L₄(2). The former uses 15.3.23 and the latter uses the four-dimensional
exclusion proved here.

The full 15.3.11 alternative supplies R = C_T(V). Conjugate generation gives
the required span containment, and relative normality gives the component core
bound. The proof keeps each original component witness and star action; the
subgroup reduction to LS remains available in `Reduction`, but no identification
of the old and new star quotients is used. Both choices of 15.3.10 are retained.

`not_four_and_not_five_of_earlier` completes the conditional 15.3.24 contract.
The explicit inputs are genuine earlier local conclusions, uniform 15.3.16–17
conclusions for the actual binary components, the full representation-theoretic
classification witnesses, and 15.3.15/22/23 on smaller outside overgroups. Their
source proofs and final discharge belong to the Section 15.3 assembly. No L₄
exclusion, module alternative, parabolic containment or MS input is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Source
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

universe u
variable {G : Type u} [Group G]

/-- The ambient conclusions of 15.3.2–8 used by the two binary exclusions.
These concern the original orthogonal action and both choices of 15.3.10. -/
structure AmbientConclusions (d : LocalData G) : Prop where
  centralizer_le : centralizer (d.V : Set G) ≤ d.M
  involution_centralizer : d.Mc = centralizer (d.Z : Set G)
  intersection : d.M ⊓ d.Mc =
    (d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G)
  residual_image : d.action.image d.Y =
    Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)
  span : localSpan d.Z d.Y = d.V
  alternatives : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
    ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action
  sylow_index : (d.S.subgroupOf (d.T : Subgroup G)).index = 2
  center_order : Nat.card d.Z = 2
  fixed_plane_order : Nat.card d.ZS = 4

/-- The preceding 15.3.16–17 conclusions needed at an actual component.
The core containment occurs in the proof of 15.3.16. The theta and Y₊
clauses are used only after the supplied model selects 15.3.17(2).
No module alternative or parabolic assertion is included. -/
structure ComponentConclusions (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : Prop where
  yplus_le : d.Yplus ≤ c.L
  component_eq_theta : c.L = theta I
  span_reduced : IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R)
  core_le : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R
  thompson : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆

variable [Finite G] {d : LocalData G} {I : Subgroup G}

/-- The L₄(2) exclusion, retaining the full earlier 15.3.11 alternative.
Its rank-two branch gives R = C_T(V), the span containment follows from
conjugate generation, and relative normality transports the intrinsic
component core. The module and MS contradictions are then constructed. -/
theorem not_four_of_earlier
    (ffClassification : Sieve.UniversalFFClassification.{u,u})
    (cohomology : Sieve.UniversalNaturalCohomology)
    (msClassification : UniversalClassification.{u})
    (ambient : AmbientConclusions d)
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2)
    (hq : IsSQTK KnownSimple.IsKnownSimple I)
    (hcontrol : SolvableInvariantControl d I)
    (h11 : OutsideStructure.Conclusions d I)
    (c : ComponentWitness d I) (hc : ComponentConclusions d c) :
    ¬ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective 4) := by
  rintro ⟨model⟩
  have hr := FiveParabolics.SourceQuotients.rankTwoCase_of_rank_two d hrank
    h11.local_structure
  have hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) :=
    hr.2.2.2.2.1
  have hLR : c.L ⊔ d.R ≤ I :=
    sup_le (component_le c) ((pCoreIn_le 2 _).trans hI.1.2)
  have hcore : c.L.pCoreIn 2 ≤ d.R :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (hLR.trans (normalizes_of_eq_theta hc.component_eq_theta))).trans hc.core_le
  have hW : d.componentSpan c.L ≤ c.L ⊔ d.R := by
    have h := span_le_overgroup d c.L hR
    simpa only [overgroup, sup_eq_left.mpr (hc.yplus_le.trans le_sup_left)] using h
  let earlier : Preparation.Earlier d c :=
    ⟨h11.sylow, hc.yplus_le, hc.component_eq_theta, h11.theta_eq.symm,
      hr.1, hr.2.1, hcontrol, hcore⟩
  exact NaturalDualElimination.exclusion_of_earlier d c ffClassification cohomology
    msClassification hI hf hrank earlier hq model hW hc.span_reduced hc.core_le
    hc.thompson (hR.le.trans inf_le_right) ambient.centralizer_le
    ambient.involution_centralizer ambient.intersection ambient.residual_image
    ambient.span ambient.alternatives (fun h => (h11.second_choice h).2.1)
    h11.characteristic_exclusion ambient.sylow_index ambient.center_order
    ambient.fixed_plane_order

/-- Both exclusions of 15.3.24 from the explicitly permitted earlier results.
The full 15.3.11 conclusions and the 15.3.16–17 component conclusions are
uniform on actual outside subgroups of I; the latter are requested only
for components with a four- or five-dimensional binary quotient. Component
existence, 15.3.22 and 15.3.23 are requested only on proper outside subgroups.
The L₄ exclusion on those subgroups is proved here, not supplied as a premise.

All classifications concern actual representations and marked quotients.
The original component witness is retained; no equality between the old
and new star quotients is needed. The five-dimensional construction proves
its parabolic is outside and that adjoining S gives a proper subgroup of I. -/
theorem not_four_and_not_five_of_earlier
    (ffClassification : Sieve.UniversalFFClassification.{u,u})
    (cohomology : Sieve.UniversalNaturalCohomology)
    (msClassification : UniversalClassification.{u})
    (ambient : AmbientConclusions d)
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2)
    (hq : IsSQTK KnownSimple.IsKnownSimple I)
    (hcontrol : SolvableInvariantControl d I)
    (h11 : ∀ K : Subgroup G, K ≤ I → K ∈ d.Hplus →
      OutsideStructure.Conclusions d K)
    (hcomponent : ∀ (K : Subgroup G), K ≤ I → K ∈ d.Hplus →
      HasCharacteristicTwo K → ∀ cK : ComponentWitness d K,
      ∀ n : ℕ, (n = 4 ∨ n = 5) →
      Nonempty ((cK.L ⧸ pCore 2 cK.L) ≃* Projective n) → ComponentConclusions d cK)
    (components : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
      SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
      Nonempty (ComponentWitness d K))
    (binary_models : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
      SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
      ∀ cK : ComponentWitness d K, ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
        Nonempty ((cK.L ⧸ pCore 2 cK.L) ≃* Projective n))
    (no_three : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
      SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
      ∀ cK : ComponentWitness d K,
        ((cK.L ⧸ pCore 2 cK.L) ≃* Projective 3) → False)
    (c : ComponentWitness d I) :
    (¬ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective 4)) ∧
      ¬ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective 5) := by
  have h11I := h11 I le_rfl hI
  have four : ∀ (K : Subgroup G), K ≤ I → K ∈ d.Hplus →
      HasCharacteristicTwo K → ∀ cK : ComponentWitness d K,
      ¬ Nonempty ((cK.L ⧸ pCore 2 cK.L) ≃* Projective 4) := by
    intro K hKI hK hfK cK hm
    have hqK : IsSQTK KnownSimple.IsKnownSimple K :=
      (IsSQTK.equiv (subgroupOfEquivOfLe hKI)).mp (hq.subgroup _)
    exact not_four_of_earlier ffClassification cohomology msClassification ambient
      hK hfK hrank hqK (solvableInvariantControl_restrict d hKI hcontrol)
      (h11 K hKI hK) cK (hcomponent K hKI hK hfK cK 4 (Or.inl rfl) hm) hm
  refine ⟨four I le_rfl hI hf c, ?_⟩
  rintro ⟨model⟩
  have hc := hcomponent I le_rfl hI hf c 5 (Or.inr rfl) ⟨model⟩
  let earlier : FiveParabolics.EarlierInputs d I :=
    { components := components
      binary_models := binary_models
      no_three := no_three
      no_four := fun K hKI hK hfK _ _ _ cK e => four K hKI.le hK hfK cK ⟨e⟩ }
  exact FiveParabolics.exclusion_of_earlier d hI h11I.sylow hf hrank hcontrol c model
    hc.yplus_le hc.component_eq_theta h11I.theta_eq.symm h11I.local_structure earlier

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Source

end
