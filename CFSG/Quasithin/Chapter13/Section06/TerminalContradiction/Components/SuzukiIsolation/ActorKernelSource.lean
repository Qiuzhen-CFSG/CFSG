module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernelStructure
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualKnownSimple

/-!
# The actor kernel on the original singular centralizer quotient

The original A₅ context supplies all prime-core exclusions in13.6.26.
Before uniqueness, an exceptional candidate and an additional component
therefore give the exact two-factor generalized Fitting subgroup in
C_G(V₁)/O₂(C_G(V₁)). Every subgroup actor in this quotient has its actual
Suzuki-conjugation kernel embedded in the exceptional automorphism group.
The Suzuki centralizer has the exceptional simple generalized Fitting
subgroup, retaining the literal intrinsic quotient equivalence.

Source: Aschbacher–Smith13.6.26–27, printed pp.934–935. These statements
do not use5.2.3, component uniqueness, or an elementary lift to C_G(V₁).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K D : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent)
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hD : D.IsCComponent) (hne : D ≠ K)
include d hCv houtside hcounter hK hc hD hne

/-- The complete two-factor and centerless structure on the original H*.
The extra component is retained throughout the conclusion. -/
theorem structure_of_context :
    let H := centralizer (V₁ : Set G)
    let q := QuotientGroup.mk' (pCore 2 H)
    fittingSubgroup (H ⧸ pCore 2 H) = ⊥ ∧
      generalizedFitting (H ⧸ pCore 2 H) = K.map q ⊔ D.map q ∧
      centralizer (generalizedFitting (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) = ⊥ ∧
      center (generalizedFitting (H ⧸ pCore 2 H)) = ⊥ := by
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hSQ := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
  have hlarge := fun p hp hlarge =>
    source_quotient_pCore_eq_bot_of_context_knownSimple d hCv houtside hcounter
      (Ratio.residualCentralizer L V₁) _ hH p hp hlarge
  have hf := fitting_bot_of_candidate hSQ hK hc hlarge
  exact ⟨hf, generalizedFitting_eq_pair hSQ hK hc hD hne hlarge,
    centerless_of_fitting_bot hf⟩

/-- The full original quotient actor has a faithful exceptional action on
the kernel of its Suzuki conjugation; it need not lift elementarily to H. -/
theorem kernel_injective_of_context [K.Normal] [D.Normal]
    (A : Subgroup ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G)))) :
    Function.Injective (action (K.map (QuotientGroup.mk' (pCore 2 _)))
      (D.map (QuotientGroup.mk' (pCore 2 _))) A) := by
  obtain ⟨hf, hF, _⟩ := structure_of_context d hCv houtside hcounter hK hc hD hne
  exact action_injective _ _ A hf hF

/-- The literal Suzuki centralizer has the exceptional generalized Fitting
subgroup, trivial center, and the actual candidate quotient marking. -/
theorem centralizer_structure_of_context [K.Normal] [D.Normal] :
    let H := centralizer (V₁ : Set G)
    let q := QuotientGroup.mk' (pCore 2 H)
    let C := centralizer (D.map q : Set (H ⧸ pCore 2 H))
    generalizedFitting C = (K.map q).subgroupOf C ∧
      center (generalizedFitting C) = ⊥ ∧
      Nonempty (generalizedFitting C ≃* (K ⧸ pCore 2 K)) := by
  let H := centralizer (V₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Kb := K.map q
  let Db := D.map q
  let C := centralizer (Db : Set (H ⧸ pCore 2 H))
  let := pCore_isNilpotent (p := 2) (G := H)
  obtain ⟨hf, hF, _⟩ := structure_of_context d hCv houtside hcounter hK hc hD hne
  have hR := radical_bot_of_fitting_bot hf
  have hKb : Kb.IsCComponent := hK.map_quotient _
  have hDb : Db.IsCComponent := hD.map_quotient _
  have hKD : Kb ≠ Db := fun he => hne (hD.eq_of_map_quotient_eq hK _ he.symm)
  have hKC : Kb ≤ C := commutator_eq_bot_iff_le_centralizer.mp
    (hKb.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hDb hKD)
  let := hc.quotient_isQuasisimple hK
  let : IsQuasisimple Kb := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hFC := centralizer_generalizedFitting Kb Db hKC hf hF
  refine ⟨hFC, ?_, ⟨(MulEquiv.subgroupCongr hFC).trans
    ((subgroupOfEquivOfLe hKC).trans (cComponentTwoCoreQuotientEquiv hK).symm)⟩⟩
  have hRC : solvableRadical C = ⊥ :=
    solvableRadical_eq_bot_of_isSubnormal hR (inferInstance : C.Normal).isSubnormal
  exact center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hRC
    (inferInstance : (generalizedFitting C).Normal).isSubnormal

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
