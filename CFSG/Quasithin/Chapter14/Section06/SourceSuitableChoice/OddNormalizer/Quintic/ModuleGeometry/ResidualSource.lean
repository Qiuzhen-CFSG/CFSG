module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualFactors
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.NaturalBorelAction

/-!
# Residual-closure geometry in the original second-normalizer argument

The original elementary module lies in O₂(H), so 14.6.12(3) puts Z in both
residual factor cores. Their opposite supports centralize the other factor.
When K_z = O²(H), the second factor core lies in O₂(K_z); hence this core is
nontrivial and maximal two-locality identifies N_G(K_z) with Mc.

The constructor below supplies all these local fields of NormalizerGeometry.
It retains four unproved ambient controls explicitly: the two prime-order
centralizer identities, the intersection index in Mc, and its two-core.
Its consumers use the literal second factor in C.2.3, source-correct component
extraction, and the normalized natural-row exclusion. They do not prove p=3.
The owner qt-e-14615-quintic-exclusion must discharge those four controls, the
exchanged PSL₂(16) geometry and the remaining model comparisons. The earlier
14.6.12--14 inputs retain final discharge with qt-e-suitable-odd-normalizer.

Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035. The source quotient
action is preserved; no ordinary-centralizer residual identification is used.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
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
private theorem original_H_le_partner : H ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action H s.outside.1 s.outside.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2

include s in
private theorem original_module_le_H_core :
    conjugateSpanBy (localModule T M) H ≤ H.pCoreIn 2 := by
  have h := source_rankTwo_f9_hypothesis s.ambient T s.empty s.maximal s.unique s.many
    s.module_card s.action s.abelian H s.outside
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    h.UH_le_H a.normalizes

include s in
/-- The full source prefix places the central point in both literal residual cores. -/
theorem source_residual_factor_point_core :
    centralInvolutions T ≤ (residual H1).pCoreIn 2 ∧
    centralInvolutions T ≤ (residual H2).pCoreIn 2 :=
  residual_factors_point_core a s.factors (original_module_le_H_core s)

include s in
/-- The original supports lie in U and ordinarily centralize the opposite residual. -/
theorem source_residual_factor_supports :
    firstSupport a H1 ≤ conjugateSpanBy (localModule T M) Mc ∧
    firstSupport a H2 ≤ conjugateSpanBy (localModule T M) Mc ∧
    firstSupport a H1 ≤ centralizer (residual H2 : Set G) ∧
    firstSupport a H2 ≤ centralizer (residual H1 : Set G) := by
  have hHZ : H ≤ centralizer (centralInvolutions T : Set G) :=
    (original_H_le_partner s).trans_eq (partner_eq_centralizer s)
  obtain ⟨h1,h2⟩ := residual_factors_centralize_opposite a s.factors hHZ
  have hUM := conjugateSpanBy_mono (le_rfl : localModule T M ≤ localModule T M)
    (original_H_le_partner s)
  exact ⟨(supportPreimage_le a _).trans hUM,(supportPreimage_le a _).trans hUM,h1,h2⟩

include s in
/-- In the residual-closure branch, maximal two-locality gives N_G(K_z) = Mc. -/
theorem source_residual_closure_normalizer (hclosure : residualClosure H Mc = residual H) :
    normalizer (residualClosure H Mc : Set G) = Mc := by
  let K := residualClosure H Mc
  let K2 := residual H2
  have hj : residual H1 ⊔ K2 = K := (residual_factors_join a s.factors).trans hclosure.symm
  have hK2 : K2 ≤ K := hj ▸ le_sup_right
  have hKN2 : K ≤ normalizer (K2 : Set G) := by
    change residualClosure H Mc ≤ normalizer (K2 : Set G)
    rw [hclosure]
    have hR0 : residual H ≤ H0 := by
      rw [←residual_factors_join a s.factors]
      exact sup_le ((residual_le H1).trans s.factors.first_le)
        ((residual_le H2).trans s.factors.second_le)
    exact hR0.trans (s.factors.normalizes_second.trans
      (normalizer_le_normalizer_characteristic_image H2 (pResidual 2 H2)))
  have hQ : K2.pCoreIn 2 ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K2) ((pCoreIn_le 2 K2).trans hK2)
      (hKN2.trans (normalizer_le_normalizer_characteristic_image K2 (pCore 2 K2)))
  have hZ : centralInvolutions T ≤ K.pCoreIn 2 := (source_residual_factor_point_core s).2.trans hQ
  have hne : K.pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hz := bot_unique (hb ▸ hZ)
    have hc := plane_centralInvolutions_card T M s.maximal.1.2 s.module_card s.action
    have hc0 : Nat.card (centralInvolutions T) = 1 := (eq_bot_iff_card _).mp hz
    omega
  have hMN : Mc ≤ normalizer (K : Set G) := le_normalizer_conjugateSpanBy _ _
  have hNQ : normalizer (K : Set G) ≤ normalizer (K.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      s.unique ▸ Set.mem_singleton Mc).1
  exact le_antisymm (hNQ.trans (hmax.2 ⟨_,hne,isPGroup_pCoreIn 2 K,rfl⟩
    (hMN.trans hNQ))) hMN

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion ComponentExclusion.ContainedComparison
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (hclosure : residualClosure H Mc = residual H)
    (hpoint : closure {x : G | x ∈ centralizer (centralInvolutions T : Set G) ∧
      orderOf x = 5} = residualClosure H Mc)
    (hconjugate : closure {x : G |
      x ∈ (residualClosure H Mc).map (MulAut.conj s.critical.endpoint.representative).toMonoidHom ⊓
        centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} =
      (residual H2).map (MulAut.conj s.critical.endpoint.representative).toMonoidHom)
    (hindex : (Mc ⊓ normalizer (residual H2 : Set G)).relIndex Mc = 2)
    (hcore : (Mc ⊓ normalizer (residual H2 : Set G)).pCoreIn 2 = Mc.pCoreIn 2)

/-- Assemble the residual branch from its four remaining ambient controls.
The factor models, supports, generators, point core, exchanged marking and
closure normalizer are proved from the original context. The four displayed
controls remain obligations of qt-e-14615-quintic-exclusion. -/
noncomputable def residualNormalizerGeometry :
    NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative := by
  exact {
    K1 := residual H1
    K2 := residual H2
    U1 := firstSupport a H1
    U2 := firstSupport a H2
    first_le := (residual_le H1).trans ((s.factors.first_le.trans s.factors.zero_le).trans
      (original_H_le_partner s))
    second_le := (residual_le H2).trans ((s.factors.second_le.trans s.factors.zero_le).trans
      (original_H_le_partner s))
    join_eq := (residual_factors_join a s.factors).trans hclosure.symm
    residual_first_le := le_rfl
    residual_second_le := le_rfl
    models := Or.inl ⟨rfl,rfl,(residual_factors_models a s.factors).1,(residual_factors_models a s.factors).2⟩
    first_support_le := le_rfl
    second_support_le := le_rfl
    first_module_le := (source_residual_factor_supports s).1
    second_module_le := (source_residual_factor_supports s).2.1
    first_centralizes := (source_residual_factor_supports s).2.2.1
    second_centralizes := (source_residual_factor_supports s).2.2.2
    first_generated := (residual_factors_generated a s.factors).1
    second_generated := (residual_factors_generated a s.factors).2
    point_closure := hpoint
    conjugate_point_closure := hconjugate
    point_core := (source_residual_factor_point_core s).2
    exchanged := residual_factors_exchanged a s.factors
    intersection_index := hindex
    intersection_core := hcore
    closure_normalizer := source_residual_closure_normalizer s hclosure }

/-- The constructed geometry uses exactly the original two residual factors. -/
theorem residualNormalizerGeometry_factors :
    let d := residualNormalizerGeometry s hclosure hpoint hconjugate hindex hcore
    d.K1 = residual H1 ∧ d.K2 = residual H2 := ⟨rfl,rfl⟩

include hclosure hpoint hconjugate hindex hcore in
/-- The actual second normalizer now needs only the four stated ambient
controls in the residual branch; all its local factor geometry is constructed. -/
theorem residual_secondNormalizer_setup :
    s.critical.endpoint.representative ∈ normalizer (residual H2 : Set G) ∧
      ¬normalizer (residual H2 : Set G) ≤ Mc ∧
      Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
        (normalizer (residual H2 : Set G)) (Mc.pCoreIn 2)
          (Mc ⊓ normalizer (residual H2 : Set G)) ∧
      ((T : Subgroup G) ⊓ normalizer (residual H2 : Set G)).relIndex T = 2 := by
  let d := residualNormalizerGeometry s hclosure hpoint hconjugate hindex hcore
  have hs := source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique s.many
    s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d
  exact ⟨hs.1,hs.2.1,hs.2.2,residual_second_normalizer_index a s.factors s.outside.1.2⟩

include hclosure hpoint hconjugate hindex hcore in
/-- Connect the constructed factor geometry to the source-correct component
extraction and the checked natural-row exclusion, using the same literal
second factor throughout. This is conditional on the four ambient controls,
not a proof of the p=3 source theorem. -/
theorem residual_component_comparison :
    Nonempty (SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2)) ∧
    ∀ j : SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2),
      Mc.pCoreIn 2 ≤ normalizer (j.J : Set G) →
        ¬Nonempty (NaturalStarRow j.J (Mc.pCoreIn 2)) := by
  let d := residualNormalizerGeometry s hclosure hpoint hconjugate hindex hcore
  refine ⟨exists_source_escaping_component s d,?_⟩
  intro j hn ⟨row⟩
  exact source_false_of_natural_row s d j hn row

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
