module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualSylow
public import Theory.SpecificGroups.GL2.SignedFiveOvergroups.Marking

/-!
# The original residual normalizer index and geometry

The actual Sylow image on K/O₂(K), for K=O²(H), is dihedral of order eight.
An injective coordinate identification puts this image in GL₂(5), where
an explicit conjugation marks it as the signed permutation subgroup.
Signed Sylow-image rigidity then makes the partner's full action image
equal to the Sylow image. The quotient-action kernel normalizes each
residual factor, so the original index two in T transfers to M_c.

This discharges the last extra premise in the residual NormalizerGeometry
constructor. The final consumers construct the literal second normalizer,
C.2.3 setup, genuine escaping component, normalized C.2.7 input and
natural-row exclusion from the original source context and K_z=K.
No full-centralizer residual identity is assumed.

The exchanged module geometry, remaining normalized component comparisons
and original p=3 conclusion still belong to qt-e-14615-quintic-exclusion.
Earlier-source 14.6.12--14 discharge remains with
qt-e-suitable-odd-normalizer. The original ExchangedFactorSetup.index is
used; this is not a proof for the weaker pair-plus-permutation-kernel input.

Source: Aschbacher--Smith, 14.6.15, printed pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
/-- Signed coordinates for the actual original Sylow action. -/
theorem source_residual_signed_coordinates (hc : residualClosure H Mc = residual H) :
    ∃ e : MulAut (residual H ⧸ pCore 2 (residual H)) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 5),
      ((T : Subgroup G).subgroupOf Mc).map (e.toMonoidHom.comp (residualPartnerAction Mc H hc)) =
        Matrix.GeneralLinearGroup.SignedFive.signedSubgroup := by
  obtain ⟨_,e0,_⟩ := source_residual_plane_coordinates s
  let S := ((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc)
  obtain ⟨d⟩ := source_residual_sylow_action_dihedral s hc
  let φ := e0.toMonoidHom.comp (S.subtype.comp d.symm.toMonoidHom)
  have hφ : Function.Injective φ := e0.injective.comp (S.subtype_injective.comp d.symm.injective)
  obtain ⟨g,hg⟩ := Matrix.GeneralLinearGroup.SignedFive.exists_signed_conjugation_of_dihedral φ hφ
  let e := e0.trans (MulAut.conj g)
  refine ⟨e,?_⟩
  have hr : φ.range = S.map e0.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem e0.toMonoidHom (d.symm x).property
    · rintro ⟨x,hx,rfl⟩
      refine ⟨d ⟨x,hx⟩,?_⟩
      change e0 (d.symm (d ⟨x,hx⟩)) = e0 x
      rw [d.symm_apply_apply]
  have hi : ((T : Subgroup G).subgroupOf Mc).map
      (e.toMonoidHom.comp (residualPartnerAction Mc H hc)) =
      φ.range.map (MulAut.conj g).toMonoidHom := by
    rw [←Subgroup.map_map]
    change S.map ((MulAut.conj g).toMonoidHom.comp e0.toMonoidHom) = _
    rw [←Subgroup.map_map,hr]
  exact hi.trans hg

include s in
/-- The residual branch's original partner-normalizer index, with no extra
matrix marking or ambient index premise. The original 14.6.12 index is used. -/
theorem source_residual_normalizer_index (hc : residualClosure H Mc = residual H) :
    (Mc ⊓ normalizer (residual H2 : Set G)).relIndex Mc = 2 := by
  obtain ⟨e,he⟩ := source_residual_signed_coordinates s hc
  exact source_residual_normalizer_index_of_signed_coordinates s hc e.toMonoidHom e.injective he

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

/-- Construct the residual geometry from the original residual-closure branch. -/
noncomputable def sourceResidualNormalizerGeometry (hc : residualClosure H Mc = residual H) :
    NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative :=
  indexedResidualNormalizerGeometry s hc (source_residual_normalizer_index s hc)

include s in
/-- The original residual branch supplies the literal second normalizer and C.2.3. -/
theorem source_residual_secondNormalizer_setup (hc : residualClosure H Mc = residual H) :
    s.critical.endpoint.representative ∈ normalizer (residual H2 : Set G) ∧
      ¬normalizer (residual H2 : Set G) ≤ Mc ∧
      Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
        (normalizer (residual H2 : Set G)) (Mc.pCoreIn 2)
          (Mc ⊓ normalizer (residual H2 : Set G)) ∧
      ((T : Subgroup G) ⊓ normalizer (residual H2 : Set G)).relIndex T = 2 :=
  indexed_residual_secondNormalizer_setup s hc (source_residual_normalizer_index s hc)

include s in
/-- Extract the actual component and its normalized C.2.7 comparison from
only the original source context and the residual-closure alternative. -/
theorem source_residual_normalized_component_comparison
    (hc : residualClosure H Mc = residual H) :
    Nonempty (SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2)) ∧
    ∀ j : SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2),
      Input KnownSimple.IsKnownSimple (normalizer (residual H2 : Set G))
        (Mc.pCoreIn 2) (Mc ⊓ normalizer (residual H2 : Set G)) j.J ∧
      ¬Nonempty (NaturalStarRow j.J (Mc.pCoreIn 2)) :=
  indexed_residual_normalized_component_comparison s hc (source_residual_normalizer_index s hc)
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
