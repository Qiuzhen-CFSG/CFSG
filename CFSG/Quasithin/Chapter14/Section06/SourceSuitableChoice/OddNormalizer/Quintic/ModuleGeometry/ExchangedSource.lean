module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedFactors

/-!
# Applying the exchanged factor geometry to the second normalizer

Use the actual PSL₂(16) components constructed from14.6.14. Once the
original residuals are marked in these components, centrality of Z in Mc
puts Z in the second component's two-core. The supports themselves suffice
as the intermediate modules in NormalizerGeometry.

The two opposite-support centralizations and the conjugated point-centralizer
identity remain explicit source module obligations. All factor models,
prime-order generators, the ordinary point-centralizer closure, normalizer
indices and core identities are proved by ExchangedFactors. The final two
theorems apply this constructor to C.2.3 and the genuine escaping component,
including the proved normalized natural-row exclusion.

These are reductions for qt-e-14615-quintic-exclusion, which retains the
module obligations and final p=3 assembly. The earlier14.6.12--14 inputs
retain final discharge with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith14.6.15, printed pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)


include s in
/-- The marked second residual places the point in the component two-core.
Only relative containment is used; no ambient normality of the component is assumed. -/
theorem source_point_core_of_second_residual_le {K : Subgroup G}
    (hKM : K ≤ Mc) (h2 : residual H2 ≤ K) : centralInvolutions T ≤ K.pCoreIn 2 := by
  have hZK := ((source_residual_factor_point_core s).2.trans (pCoreIn_le 2 _)).trans h2
  have hn : K ≤ normalizer (centralInvolutions T : Set G) :=
    (hKM.trans_eq (partner_eq_centralizer s)).trans (Subgroup.centralizer_le_normalizer _)
  exact le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2
    (conjugateSpanBy (localModule T M) H)).to_le a.kernel_le) hZK hn

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T))
    (hfirst : residual H1 ≤ b.K1) (hsecond : residual H2 ≤ b.K2)
    (hcent1 : firstSupport a H1 ≤ centralizer (b.K2 : Set G))
    (hcent2 : firstSupport a H2 ≤ centralizer (b.K1 : Set G))
    (hconjugate : closure {x : G |
      x ∈ (residualClosure H Mc).map (MulAut.conj s.critical.endpoint.representative).toMonoidHom ⊓
        centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} =
      b.K2.map (MulAut.conj s.critical.endpoint.representative).toMonoidHom)

/-- Assemble the exchanged branch with its actual component models and
normalizer controls proved. Only the source module marking, opposite-support
centralization and conjugated point-centralizer identity remain explicit.
Their discharge and the final p=3 proof belong to qt-e-14615-quintic-exclusion. -/
noncomputable def exchangedNormalizerGeometry :
    NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative where
  K1 := b.K1
  K2 := b.K2
  U1 := firstSupport a H1
  U2 := firstSupport a H2
  first_le := b.first_le
  second_le := b.second_le
  join_eq := b.join_eq
  residual_first_le := hfirst
  residual_second_le := hsecond
  models := Or.inr ⟨b.first_component,b.second_component,b.first_model,b.second_model⟩
  first_support_le := le_rfl
  second_support_le := le_rfl
  first_module_le := (source_residual_factor_supports s).1
  second_module_le := (source_residual_factor_supports s).2.1
  first_centralizes := hcent1
  second_centralizes := hcent2
  first_generated := b.first_generated
  second_generated := b.second_generated
  point_closure := b.point_closure
  conjugate_point_closure := hconjugate
  point_core := source_point_core_of_second_residual_le s b.second_le hsecond
  exchanged := b.exchanged
  intersection_index := b.second_index
  intersection_core := b.intersection_core
  closure_normalizer := b.closure_normalizer

/-- The constructor retains both original components. -/
theorem exchangedNormalizerGeometry_factors :
    let d := exchangedNormalizerGeometry s b hfirst hsecond hcent1 hcent2 hconjugate
    d.K1 = b.K1 ∧ d.K2 = b.K2 := ⟨rfl,rfl⟩


include hfirst hsecond hcent1 hcent2 hconjugate in
/-- Apply the exchanged geometry to the literal C.2.3 normalizer, retaining
the source critical-pair element and the original Sylow subgroup. -/
theorem exchanged_secondNormalizer_setup :
    s.critical.endpoint.representative ∈ normalizer (b.K2 : Set G) ∧
      ¬normalizer (b.K2 : Set G) ≤ Mc ∧
      Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
        (normalizer (b.K2 : Set G)) (Mc.pCoreIn 2)
          (Mc ⊓ normalizer (b.K2 : Set G)) ∧
      ((T : Subgroup G) ⊓ normalizer (b.K2 : Set G)).relIndex T = 2 := by
  let d := exchangedNormalizerGeometry s b hfirst hsecond hcent1 hcent2 hconjugate
  have hs := source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique s.many
    s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d
  exact ⟨hs.1,hs.2.1,hs.2.2,b.sylow_index⟩

include hfirst hsecond hcent1 hcent2 hconjugate in
/-- The exchanged branch feeds genuine component extraction and the proved
normalized natural-row contradiction. The remaining source comparisons and
module premises retain final discharge with qt-e-14615-quintic-exclusion. -/
theorem exchanged_component_comparison :
    Nonempty (SourceEscapingComponent Mc (residualClosure H Mc)
      b.K1 b.K2 (Mc.pCoreIn 2)) ∧
    ∀ j : SourceEscapingComponent Mc (residualClosure H Mc) b.K1 b.K2 (Mc.pCoreIn 2),
      Mc.pCoreIn 2 ≤ normalizer (j.J : Set G) →
        ¬Nonempty (ContainedComparison.NaturalStarRow j.J (Mc.pCoreIn 2)) := by
  let d := exchangedNormalizerGeometry s b hfirst hsecond hcent1 hcent2 hconjugate
  refine ⟨exists_source_escaping_component s d,?_⟩
  intro j hn ⟨row⟩
  exact source_false_of_natural_row s d j hn row

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
