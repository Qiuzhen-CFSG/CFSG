module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta

/-!
# Original local inputs to the binary parabolic reduction

The original natural action and Sylow flag construct both parabolic models.
The cubic theta identity gives relative normality in H ∩ M. The covered
factorization and normalizer theorem supply the two distinct node residuals.
Only the preceding 13.8.21 component conclusions remain explicit; in
particular their set product, rather than just a generated join, proves
relative component normality. The original solvable-overgroup theorem
discharges the 13.8.13 premise.

Source: Aschbacher–Smith, 13.8.25, printed pp.959–960, using 13.2.2,
13.7.3(9), 13.8.13 and 13.8.21. The component conclusions are produced by
the separate original 13.8.19–21 argument.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open TransvectionRecognition.Component.ModelExtension
open SourceCompletion
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Chapter1.Section02.LocalModels
open Chapter2.ComponentRefinement.LieType.Binary
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The used clauses of the preceding 13.8.21, on every actual overgroup.
The product is the source set product, not a bare subgroup join. -/
structure ComponentConclusions (L₁ T G₁ M : Subgroup G) : Prop where
  base_le : ∀ {H K : Subgroup G}, H ∈ Source.Hz L₁ T G₁ M → K ≤ H →
    (K.subgroupOf H).IsCComponent → L₁ ≤ K
  models : ∀ {H K : Subgroup G}, H ∈ Source.Hz L₁ T G₁ M → K ≤ H →
    (K.subgroupOf H).IsCComponent →
    (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) ∨
      IsAlternating (K ⧸ pCore 2 K) 6 ∨ IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
  product : ∀ {H K : Subgroup G}, H ∈ Source.Hz L₁ T G₁ M → K ≤ H →
    (K.subgroupOf H).IsCComponent → (H : Set G) = (K : Set G) * (T : Set G)
  three_automorphisms : ∀ (H K : Subgroup G), H ∈ Source.Hz L₁ T G₁ M → K ≤ H →
    (K.subgroupOf H).IsCComponent → Nonempty ((K ⧸ pCore 2 K) ≃* PSL 3) →
    Nonempty (Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL)

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The ordinary/covered parabolic alternatives with the original flag. -/
theorem local_action :
    Nonempty (Parabolics.OrdinarySource.NaturalSetup L (T : Subgroup G) V V₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)) := by
  rcases local_quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl (LocalFitting.ordinary_natural d e he)
  · refine Or.inr ⟨?_, local_covered_flag_model d e he⟩
    exact ⟨local_quotient_quasisimple d,
      (Nat.card_congr (centerCongr e).toEquiv).trans Representation.Hexacode.even_center_card,
      ⟨local_central_quotient d⟩⟩

private theorem covered_natural
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
  rcases OriginalSource.local_action d with ha | ⟨_, ha⟩
  · obtain ⟨a⟩ := ha
    have hz := Nat.card_congr (centerCongr a.model).toEquiv
    rw [hc.2.1, alternatingGroup.center_eq_bot (by simp), card_bot] at hz
    omega
  · exact ha

/-- All local, residual and solvable-overgroup fields of the parabolic
consumer are constructed from the original setup and earlier source inputs. -/
theorem group_facts
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
    (components : ComponentConclusions (one L T V₁) T G₁ M) :
    SourceReduction.GroupFacts L (one L T V₁) T V V₁ V₃ G₁ M := by
  have hM : L ⊔ (T : Subgroup G) ≤ M := by
    rw [d.local_normalizer]
    exact sup_le L.le_normalizer d.normalizes_L
  have htheta (H : Subgroup G) (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) :
      one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3} :=
    (Section07.ModelExclusions.theta_intersection (localNaturalSetup d) h hH).symm
  refine {
    local_definition := rfl
    local_action := local_action d
    base_le_M := hM
    theta := htheta
    local_normal := ?_
    covered_factor := ?_
    covered_normalizer := ?_
    solvable_overgroups := SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource
    base_le_component := components.base_le
    component_list := components.models
    supplement := ?_
    component_normal := ?_
    three_automorphisms := components.three_automorphisms }
  · intro H hH
    apply (normal_subgroupOf_iff_le_normalizer
      (le_inf (le_sup_left.trans hH.1.2) ((one_le L T V₁).trans (inf_le_left.trans hM)))).mpr
    rw [htheta H hH]
    apply le_normalizer_closure_iff.mpr
    intro g hg x hx
    exact subset_closure ⟨(H ⊓ M).mul_mem ((H ⊓ M).mul_mem hg hx.1) ((H ⊓ M).inv_mem hg),
      ((MulAut.conj g).orderOf_eq x).trans hx.2⟩
  · intro hc
    obtain ⟨a⟩ := covered_natural d hc
    exact CoverFactorization.source_factorization a
  · intro hc
    obtain ⟨a⟩ := covered_natural d hc
    rw [a.zero_normalizer_eq h, ← d.local_normalizer]
  · intro H K hH hKH hK
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (K : Set G) * ((T : Subgroup G) : Set G) := by
        rw [← components.product hH hKH hK]
        exact hx
      obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hx'
      exact mul_mem (mem_sup_left hk) (mem_sup_right ht)
    · exact sup_le hKH (le_sup_right.trans hH.1.2)
  · intro H K hH hKH hK
    exact component_normal_of_product T (le_sup_right.trans hH.1.2) hKH hK
      (components.product hH hKH hK)

/-- The actual source application excludes L₃(2) and L₅(2) in both
critical cases. Only the marked middle-node action can still obstruct the
covered local quotient and the L₄(2) model of H*. -/
theorem parabolic_reduction
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
    (components : ComponentConclusions (one L T V₁) T G₁ M)
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    ∃ hn : n = 4,
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        Nonempty (Source.Hstar H ≃* PSL 4)) ∨
      Parabolics.MiddleNodeMarking H K (one L T V₁) T hKH hK (hn ▸ e) := by
  have groups := group_facts d h hF9all hcentral hcomm hsource components
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨hn, halt⟩ := Parabolics.source_parabolic_reduction H K L (one L T V₁) T
    V V₁ V₃ G₁ M rfl groups.local_action hH groups.base_le_M hKH hK
    (groups.component_normal hH hKH hK) hT (groups.supplement hH hKH hK).symm
    (groups.theta H hH) (groups.local_normal H hH) groups.covered_factor
    groups.covered_normalizer groups.solvable_overgroups
    (fun J C hJ hCJ hC => components.base_le hJ hCJ hC) components.three_automorphisms
    hn₀ hn₁ e
  refine ⟨hn, ?_⟩
  rcases halt with ⟨hc, he, _⟩ | ⟨_, hm⟩
  · exact Or.inl ⟨hc, he⟩
  · exact Or.inr hm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
