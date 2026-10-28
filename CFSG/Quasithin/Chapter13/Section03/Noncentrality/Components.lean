module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Quotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Reduced
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.GroupTheory.CComponent.Basic

/-!
# Components in the noncentrality argument

This file is the source-shaped leaf for parts (e)--(g) of Lemma 13.3.14.  The
component is kept in the original group `G`; in particular, `J`, `R₂(J)` and
`[R₂(J), K]` are literal subgroups of `G`.  The universal B.5.6 implication and
the small model calculation are parameters of the source application.  They
are stated with their actual action and quotient data, so the application does
not hide a component-placement or module-classification assumption.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Lemma 13.3.14,
printed pp.892--893 (PDF pp.909--910), together with 1.3.7, 1.4.1.4, 3.1.8.3,
B.5.6, A.4.7--A.4.8.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter12.Section02
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality

universe u
variable {G : Type u} [Group G]

/-- The normalizer information supplied by 13.3.2 and the maximal-local
uniqueness theorem.  The two implication fields are the exact uses of those
earlier results in the printed proof: they are not conclusions of this leaf.
-/
structure ComponentNormalizerInput
    (T M L Lplus G1 Q1 U K MKT : Subgroup G) : Prop where
  k_le_g1 : K ≤ G1
  k_component : (K.subgroupOf G1).IsCComponent
  lplus_normalizes : Lplus ≤ normalizer (K : Set G)
  k_generated : ⁅K, Lplus⁆ = K
  k_quotient_quasisimple : IsQuasisimple (K ⧸ pCore 2 K)
  /-- Reduction (b), `[U,K] ≠ 1`, is the actual input to A.4.9. -/
  uK_noncentral : ⁅U, K⁆ ≠ ⊥
  /-- Reduction (a), retaining the original omega-center subgroup. -/
  u_in_omega_center : U ≤ Stellmacher.omegaOneCenterAmbient Q1
  /-- A.4.9 and 13.3.2.2, with their source hypotheses still explicit. -/
  faithful_maximal_of_source :
    ⁅U, K⁆ ≠ ⊥ → U ≤ Stellmacher.omegaOneCenterAmbient Q1 →
      K ∈ Chapter1.LStar G T
  /-- The normalizer conclusion of 13.3.2.2. -/
  normalizer_of_source : K ∈ Chapter1.LStar G T →
    G1 ≤ normalizer (K : Set G) ∧ normalizer (K : Set G) = MKT
  g1_not_le_m : ¬ G1 ≤ M
  /-- The `!M(LT)` uniqueness implication used to exclude `L ≤ N_G(K)`. -/
  local_le_m_of_le_normalizer : L ≤ normalizer (K : Set G) → G1 ≤ M
  /-- The `!M(KT)` uniqueness implication used to exclude `K ≤ M`. -/
  normalizer_eq_of_k_le_m : K ≤ M → normalizer (K : Set G) = M

/-- The original flag data retained by the component and five-dimensional
calculation.  `Y` is kept as the actual subgroup used in reduction (b); no
replacement flag or quotient is introduced here. -/
structure ComponentFlags (V1 V2 V3 Y : Subgroup G) : Prop where
  v1_le_v3 : V1 ≤ V3
  y_normalizes_v3 : Y ≤ normalizer (V3 : Set G)

/-- The literal B.5.6 alternatives for the action on `[W,K]`.  The first
alternative deliberately retains all three single-module rows, including the
five-dimensional deleted permutation module for `A₆`.
-/
inductive ComponentModuleAlternative
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) : Prop
  | singleLinearTwo (F : BinaryField)
      (natural : IsLinearNatural ρ F 2) : ComponentModuleAlternative ρ
  | singleSymmetricFive
      (natural : IsSymmetricNatural ρ 5) : ComponentModuleAlternative ρ
  | singleLinearThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsLinearNatural ρ F 3) : ComponentModuleAlternative ρ
  | doubledNatural (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsRepeatedLinearNatural ρ F 3 2) :
      ComponentModuleAlternative ρ

/-- The literal conjugation action of `J` on `WK`. -/
def componentAction (_T _Lplus _K J _W WK : Subgroup G)
    (hJ : J ≤ normalizer (WK : Set G)) : J →* MulAut WK :=
  WK.normalizerMonoidHom.comp
    (J.subtype.codRestrict (normalizer (WK : Set G)) (fun x => hJ x.property))

/-- The elementary-perfect representation on the actual subgroup `WK`. -/
def componentRepresentation (_T _Lplus _K J _W WK : Subgroup G)
    (hJ : J ≤ normalizer (WK : Set G))
    (hWK : IsElementaryAbelian 2 WK) :
    Representation (ZMod 2) J (Additive WK) :=
  letI := hWK
  Representation.elementaryRepresentation (componentAction _T _Lplus _K J _W WK hJ)

/-- The image in `G` of the reduced-two subgroup of a subgroup of `G`. -/
def reducedTwoImage (H : Subgroup G) : Subgroup G :=
  (reducedTwoSubgroup H).map H.subtype

/-- Actual data on `J = K Lplus T`.  Every subgroup in the action is a
subgroup of `G`; no quotient or abstract replacement is used.

The `classifier` field is the universal B.5.6 source implication specialized
to this literal action.  Its premise is the full `FFHypothesis`, including
finiteness, faithfulness, trivial two-core, offender generation and the SQTK
cover.  The source theorem that supplies this implication remains explicit for
the final Chapter-13 assembly.
-/
structure ComponentModuleInput
    (T JT Lplus K J W WK R2KT : Subgroup G) (𝒦 : GroupClass.{u}) [Finite G] : Type (u + 1) where
  j_eq : J = K ⊔ Lplus ⊔ T
  /-- `W` is the actual image of `R₂(J)` in the original ambient group. -/
  w_eq : W = reducedTwoImage J
  wk_eq : WK = ⁅W, K⁆
  j_normalizes_wk : J ≤ normalizer (WK : Set G)
  wk_elementary : IsElementaryAbelian 2 WK
  jt_eq : JT = Stellmacher.elementaryAbelianMaxJ T
  k_generated : K = ⁅K, JT⁆
  /-- The inherited `R₂(KT) ≤ R₂(J)` containment from A.1.11. -/
  r2_kt_eq : R2KT = reducedTwoImage (K ⊔ T)
  r2_kt_le_w : R2KT ≤ W
  action : Representation (ZMod 2) J (Additive WK)
  action_eq : action =
    componentRepresentation T Lplus K J W WK j_normalizes_wk wk_elementary
  finite_module : Module.Finite (ZMod 2) (Additive WK)
  action_faithful : Function.Injective action
  two_core : pCore 2 J = ⊥
  offender_generated : offenderSubgroup action = ⊤
  quotient : Nonempty (SQTKQuotient 𝒦 J)
  /-- The universal B.5.6 implication, with every field of `FFHypothesis`
  passed explicitly. -/
  classifier : Module.Finite (ZMod 2) (Additive WK) →
    Function.Injective action → pCore 2 J = ⊥ →
    offenderSubgroup action = ⊤ → Nonempty (SQTKQuotient 𝒦 J) →
    ComponentModuleAlternative
    (show Representation (ZMod 2) (K.subgroupOf J) (Additive WK) from
      action.comp (K.subgroupOf J).subtype)

/-! ### The normalizer reductions (e) and (f) -/

theorem reduction_e
    (T M L Lplus G1 Q1 U K MKT : Subgroup G)
    (h : ComponentNormalizerInput T M L Lplus G1 Q1 U K MKT) :
    K ∈ Chapter1.LStar G T ∧
      G1 ≤ normalizer (K : Set G) ∧
      normalizer (K : Set G) = MKT ∧
      ¬ L ≤ normalizer (K : Set G) ∧
      ¬ K ≤ M := by
  have hfaithful : K ∈ Chapter1.LStar G T :=
    h.faithful_maximal_of_source h.uK_noncentral h.u_in_omega_center
  have hnormalizer := h.normalizer_of_source hfaithful
  have hproper : normalizer (K : Set G) ≠ M := by
    intro heq
    apply h.g1_not_le_m
    rw [← heq]
    exact hnormalizer.1
  have hL : ¬ L ≤ normalizer (K : Set G) := by
    intro hL
    exact h.g1_not_le_m (h.local_le_m_of_le_normalizer hL)
  have hK : ¬ K ≤ M := by
    intro hK
    exact hproper (h.normalizer_eq_of_k_le_m hK)
  exact ⟨hfaithful, hnormalizer.1, hnormalizer.2, hL, hK⟩

theorem reduction_f
    (T M L Lplus G1 Q1 U K MKT L1 L2 : Subgroup G)
    (h : ComponentNormalizerInput T M L Lplus G1 Q1 U K MKT)
    (hL1 : L1 ≤ normalizer (K : Set G))
    (hLjoin : L = L1 ⊔ L2) :
    ¬ L2 ≤ normalizer (K : Set G) := by
  intro hL2
  apply (reduction_e T M L Lplus G1 Q1 U K MKT h).2.2.2.1
  rw [hLjoin]
  exact sup_le hL1 hL2

/-! ### The literal FF-module action -/

theorem module_analysis
    (T JT Lplus K J W WK R2KT : Subgroup G) (𝒦 : GroupClass.{u}) [Finite G]
    (h : ComponentModuleInput T JT Lplus K J W WK R2KT 𝒦) :
    letI := h.wk_elementary
    ComponentModuleAlternative
      (show Representation (ZMod 2) (K.subgroupOf J) (Additive WK) from
        h.action.comp
          (K.subgroupOf J).subtype) := by
  simpa [h.action_eq] using h.classifier h.finite_module h.action_faithful
    h.two_core h.offender_generated h.quotient

/-! ### The five-dimensional exclusion and (g) -/

/-- The actual five-dimensional `A₆` calculation used after the nontrivial
centralizer branch of B.5.6.  It records the line in `WK/V₁` and its preimage;
the contradiction is proved below from the original commutator identity.
-/
structure FiveDimensionalA6Input
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (V1 V3 Lplus WK : Subgroup G) where
  v1_ne_bot : V1 ≠ ⊥
  v1_le_v3 : V1 ≤ V3
  v3_le_wk : V3 ≤ WK
  action : IsSymmetricNatural ρ 5
  /-- `A₄` supplies the invariant line in the quotient. -/
  line_preimage : Subgroup G
  v3_le_line_preimage : V3 ≤ line_preimage
  /-- The five-dimensional calculation centralizes this preimage by the
two-core of `Lplus`. -/
  centralizes_preimage : ⁅line_preimage, Lplus.pCoreIn 2⁆ = ⊥
  /-- The original flag geometry, `[V₃,O₂(Lplus)] = V₁`. -/
  commutator_eq_v1 : ⁅V3, Lplus.pCoreIn 2⁆ = V1

/-- The model calculation turns the noncentralizer alternative into the
five-dimensional input.  This is the precise earlier model theorem consumed by
the present source application; it does not contain the desired conclusion
`Lplus ≤ K → False`.
-/
theorem five_dimensional_contradiction
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (V1 V3 Lplus WK : Subgroup G)
    (d : FiveDimensionalA6Input ρ V1 V3 Lplus WK) : False := by
  apply d.v1_ne_bot
  apply bot_unique
  have hle : ⁅V3, Lplus.pCoreIn 2⁆ ≤
      ⁅d.line_preimage, Lplus.pCoreIn 2⁆ :=
    commutator_mono d.v3_le_line_preimage le_rfl
  rw [d.commutator_eq_v1, d.centralizes_preimage] at hle
  exact hle

theorem reduction_g
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (V1 V2 V3 Y Lplus K WK : Subgroup G)
    (flags : ComponentFlags V1 V2 V3 Y)
    (hmodel : Lplus ≤ K → ComponentFlags V1 V2 V3 Y →
      Nonempty (FiveDimensionalA6Input ρ V1 V3 Lplus WK)) :
    ¬ Lplus ≤ K := by
  intro hL
  obtain ⟨d⟩ := hmodel hL flags
  exact five_dimensional_contradiction ρ V1 V3 Lplus WK d

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
