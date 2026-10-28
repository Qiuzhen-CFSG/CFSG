module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import Theory.GroupTheory.FourGroupNormalizerOvergroup
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.Mathieu.M22.Properties.FourNormalizers
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.FourNormalizers
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Reduction
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups

/-!
# The remaining Mathieu branches of the sporadic rank-one sieve

A subgroup maximal subject to F* = O₂ cannot normalize a four-group whose
full ambient normalizer has a strict overgroup with the same characteristic-two
property. This reduces the model inspection to concrete normalizer geometry.
The reduction transports genuine ambient equivalences: M₂₂ has its inner and
full design-automorphism cases, while all automorphisms of M₂₃ and M₂₄ are inner.

The native calculations supply exhaustive four-group coverage and strict
characteristic-two overgroups: hexad stabilizers for M₂₂ and its outer extension,
heptad stabilizers for M₂₃, and octad or trio stabilizers for the three M₂₄ rows.
The final exclusions discharge every geometric premise of the conditional
reductions, and apply also to the actual component image in I/C_I(L).
Source: Aschbacher--Smith, combined manuscript (1 March 2004), the sporadic
paragraph of 15.3.43, printed p.1140, and 1.1.5(3)(f), printed p.502.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G]

/-- Reduce the exact source configuration to the intrinsic normalizer geometry. -/
theorem LocalConfiguration.false_of_fourNormalizerOvergroups
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (h : FourNormalizerOvergroups G) : False := by
  obtain ⟨P, rfl⟩ := c.sylow
  exact h.not_normalized_by_maximal P M V c.sylow_le_local c.plane_le_sylow
    ((normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal)
    c.plane_elementary c.plane_card c.maximal

/-- The full commutator condition places the four-group inside the actual
normal component, including when the ambient group has outer automorphisms. -/
theorem LocalConfiguration.plane_le_component
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V) : V ≤ K := by
  let : K.Normal := c.normal
  rw [← c.plane_commutator]
  exact (commutator_mono le_rfl c.y_le_component).trans (commutator_le_right V K)

/-- The outer-extension branch needs geometry only for four-groups inside K. -/
theorem LocalConfiguration.false_of_component_fourNormalizerOvergroups
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (h : FourNormalizerOvergroupsIn K) : False := by
  obtain ⟨P, rfl⟩ := c.sylow
  have hn : M ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal
  obtain ⟨D, hD, hf⟩ := h P V c.plane_le_component c.plane_le_sylow
    (c.sylow_le_local.trans hn) c.plane_elementary c.plane_card
  exact hD.not_ge ((c.maximal.2 hf (hn.trans hD.le)).trans hn)

private theorem ambient_equiv_of_inner {D : Type*} [Group D]
    {K : Subgroup G} (hn : K.Normal) (hc : centralizer (K : Set G) = ⊥)
    (e : K ≃* D) (hi : Function.Surjective (MulAut.conj : D →* MulAut D)) :
    Nonempty (G ≃* D) := by
  let : K.Normal := hn
  have hK : K = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨d, hd⟩ := hi ((MulAut.congr e) (MulAut.conjNormal x))
    have hk : MulAut.conjNormal x = MulAut.conj (e.symm d) := by
      apply (MulAut.congr e).injective
      rw [MulAut.congr_conj, e.apply_symm_apply]
      exact hd.symm
    have hx : x = (e.symm d : G) :=
      MulAut.conjNormal_injective_of_centralizer_eq_bot K hc
        (hk.trans MulAut.conjNormal_val.symm)
    exact hx ▸ (e.symm d).property
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hK.symm).trans e)⟩

variable [Finite G]

/-- Both possible faithful M₂₂ ambients are retained in the geometric reduction. -/
theorem LocalConfiguration.not_mathieu_twentyTwo_of_normalizer_overgroups
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.Mathieu.M22)
    (hin : FourNormalizerOvergroups Sporadic.Mathieu.M22)
    (hout : FourNormalizerOvergroupsIn Sporadic.Mathieu.M22ValueBound.Concrete.inner) : False := by
  let : K.Normal := c.normal
  rcases Sporadic.Mathieu.M22ValueBound.Concrete.ambient_equiv_alternatives K
      c.faithful e with ⟨_, ⟨f⟩⟩ | ⟨f, hf⟩
  · exact c.false_of_fourNormalizerOvergroups (hin.of_mulEquiv f)
  · exact c.false_of_component_fourNormalizerOvergroups
      (FourNormalizerOvergroupsIn.of_mulEquiv f K (hf ▸ hout))

/-- All abstract M₂₃ automorphisms are inner, so the native normalizer calculation
covers every allowed faithful ambient extension. -/
theorem LocalConfiguration.not_mathieu_twentyThree_of_normalizer_overgroups
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.Mathieu.M23)
    (h : FourNormalizerOvergroups Sporadic.Mathieu.M23) : False := by
  obtain ⟨f⟩ := ambient_equiv_of_inner c.normal c.faithful e
    Sporadic.Mathieu.m23_conj_surjective
  exact c.false_of_fourNormalizerOvergroups (h.of_mulEquiv f)

/-- The native M₂₄ normalizer calculation covers every faithful normal copy,
using the proved full abstract-automorphism innerness theorem. -/
theorem LocalConfiguration.not_mathieu_twentyFour_of_normalizer_overgroups
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.Mathieu.M24)
    (h : FourNormalizerOvergroups Sporadic.Mathieu.M24) : False := by
  obtain ⟨f⟩ := ambient_equiv_of_inner c.normal c.faithful e
    Sporadic.Mathieu.M24OuterRestriction.conj_surjective
  exact c.false_of_fourNormalizerOvergroups (h.of_mulEquiv f)

/-- The source M₂₄ branch reduces to the three explicit normalizer calculations;
all coverage, source-to-model transport, and maximality steps are discharged. -/
theorem LocalConfiguration.not_mathieu_twentyFour_of_three_rows
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.Mathieu.M24)
    (h : ∀ i : Fin 22, i = 1 ∨ i = 2 ∨ i = 3 →
      ∃ D : Subgroup Sporadic.Mathieu.M24,
        normalizer (Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.ambient i :
          Set Sporadic.Mathieu.M24) < D ∧ generalizedFitting D = pCore 2 D) : False :=
  c.not_mathieu_twentyFour_of_normalizer_overgroups e
    (Sporadic.Mathieu.M24LocalGeometry.FourNormalizers.fourNormalizerOvergroups_of_rows h)

/-- A faithful normal M₂₂ cannot support the source local configuration,
including in the full outer extension. Both native normalizer calculations
are supplied, and the commutator condition places V in the inner subgroup. -/
theorem LocalConfiguration.not_mathieu_twentyTwo
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.Mathieu.M22) : False :=
  c.not_mathieu_twentyTwo_of_normalizer_overgroups e
    Sporadic.Mathieu.M22FourNormalizers.fourNormalizerOvergroups
    Sporadic.Mathieu.M22FourNormalizers.fourNormalizerOvergroupsIn

/-- A faithful normal M₂₃ cannot support the source local configuration.
Exhaustive native four-group coverage and automorphism innerness discharge
the geometric and ambient premises. -/
theorem LocalConfiguration.not_mathieu_twentyThree
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.Mathieu.M23) : False :=
  c.not_mathieu_twentyThree_of_normalizer_overgroups e
    Sporadic.Mathieu.M23Geometry.fourNormalizerOvergroups

/-- A faithful normal M₂₄ cannot support the source local configuration.
The three explicit normalizer enlargements exhaust its Sylow-normal
four-groups, and automorphism innerness covers every faithful ambient. -/
theorem LocalConfiguration.not_mathieu_twentyFour
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.Mathieu.M24) : False :=
  c.not_mathieu_twentyFour_of_three_rows e
    Sporadic.Mathieu.M24LocalGeometry.FourNormalizers.three_normalizer_overgroups

/-- Exclude M₂₂ for the actual component image in I/C_I(L), retaining the
original component and its possible central cover. -/
theorem reduced_not_mathieu_twentyTwo {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Sporadic.Mathieu.M22) : False :=
  (localConfiguration_of_reduced c).not_mathieu_twentyTwo e

/-- Exclude M₂₃ for the actual component image in I/C_I(L). -/
theorem reduced_not_mathieu_twentyThree {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Sporadic.Mathieu.M23) : False :=
  (localConfiguration_of_reduced c).not_mathieu_twentyThree e

/-- Exclude M₂₄ for the actual component image in I/C_I(L). -/
theorem reduced_not_mathieu_twentyFour {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Sporadic.Mathieu.M24) : False :=
  (localConfiguration_of_reduced c).not_mathieu_twentyFour e

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
