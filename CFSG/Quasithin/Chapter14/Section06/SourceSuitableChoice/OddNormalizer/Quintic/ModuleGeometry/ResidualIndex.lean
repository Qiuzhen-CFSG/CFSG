module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualNormalized
public import Theory.SpecificGroups.GL2.SignedFiveOvergroups
public import Theory.GroupTheory.PCoreNormalizerAction.ResidualNormalizer
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates

/-!
# The residual normalizer from the literal quotient action

When K_z = O²(H), the original partner normalizes K = O²(H). Its action
on K/O₂(K) has a kernel that normalizes both two-perfect residual factors;
this uses quotient triviality, without asserting ordinary centralization.
A signed Sylow marking in GL₂(5) makes the full image equal to the Sylow
image. The normalizer index therefore transfers from T to the partner.

The final consumers supply all residual NormalizerGeometry fields and the
literal C.2.3 and C.2.7 applications under that marking. ResidualSigned constructs the
marking from the original source context. The exchanged module geometry,
remaining normalized component comparisons and final p=3 assembly remain
with qt-e-14615-quintic-exclusion. The original 14.6.12 index is still used;
this does not establish a proof without ExchangedFactorSetup.index.
Earlier-source 14.6.12--14 discharge remains with
qt-e-suitable-odd-normalizer.

Source: Aschbacher--Smith, 14.6.15, printed pp.1034--1035.
-/

@[expose] public section
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

omit [Finite G] in
/-- The residual branch's original closure equality gives ambient normalization. -/
theorem residual_partner_normalizes (Mc H : Subgroup G)
    (hc : residualClosure H Mc = residual H) : Mc ≤ normalizer (residual H : Set G) := by
  rw [←hc]
  exact le_normalizer_conjugateSpanBy _ _

/-- Conjugation by the literal partner on the intrinsic residual two-core quotient. -/
noncomputable def residualPartnerAction (Mc H : Subgroup G)
    (hc : residualClosure H Mc = residual H) : Mc →* MulAut (residual H ⧸ pCore 2 (residual H)) :=
  (pCoreNormalizerAction 2 (residual H)).comp (inclusion (residual_partner_normalizes Mc H hc))

include s in
/-- The original ambient Sylow is contained in the original partner. -/
theorem source_residual_partner_sylow_le : (T : Subgroup G) ≤ Mc := by
  rw [partner_eq_centralizer s]
  exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)

include s in
/-- The actual residual quotient is the elementary five-plane; it has marked
coordinates for its full automorphism group. No Sylow-image marking is asserted. -/
theorem source_residual_plane_coordinates :
    ∃ (c : (residual H ⧸ pCore 2 (residual H)) ≃* Multiplicative (Fin 2 → ZMod 5))
      (e : MulAut (residual H ⧸ pCore 2 (residual H)) ≃*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)),
      ∀ α v, Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.planeAction 5 (e α) (c v) =
        c (α v) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := s.primitive.elementary
  obtain ⟨q,_⟩ := residual_quotient_equiv (by decide : Odd 5) H
    (IsElementaryAbelian.isPGroup 5 (pResidual 2 (H ⧸ pCore 2 H)))
  let : IsElementaryAbelian 5 (residual H ⧸ pCore 2 (residual H)) :=
    IsElementaryAbelian.of_surjective q.symm.toMonoidHom q.symm.surjective
  apply Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates
  exact (Nat.card_congr q.toEquiv).trans s.factors.residual_card

include s in
/-- The literal quotient-action kernel normalizes both residual factors,
without an ordinary-centralizer assertion. -/
theorem source_residual_action_kernel_normalizes
    (hc : residualClosure H Mc = residual H) :
    (residualPartnerAction Mc H hc).ker.map Mc.subtype ≤ normalizer (residual H1 : Set G) ∧
    (residualPartnerAction Mc H hc).ker.map Mc.subtype ≤ normalizer (residual H2 : Set G) := by
  have hHM : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
      s.many s.module_card s.action H s.outside.1 s.outside.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hcore : (residual H).pCoreIn 2 ≤ Mc.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes ((residual_le H).trans hHM) (residual_partner_normalizes Mc H hc)
  have hn := source_residual_core_normalizes_factors s hc
  have aux (A : Subgroup G) (hA : A ≤ residual H) (hp : IsPPerfect 2 A)
      (hQA : Mc.pCoreIn 2 ≤ normalizer (A : Set G)) :
      (residualPartnerAction Mc H hc).ker.map Mc.subtype ≤ normalizer (A : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    apply pCoreNormalizerAction_kernel_normalizes (residual H) A hA hp (hcore.trans hQA)
    exact ⟨inclusion (residual_partner_normalizes Mc H hc) y,hy,rfl⟩
  exact ⟨aux _ ((residual_factors_join a s.factors) ▸ le_sup_left)
    (isPPerfect_embedded_pResidual 2 H1) hn.1,
    aux _ ((residual_factors_join a s.factors) ▸ le_sup_right)
    (isPPerfect_embedded_pResidual 2 H2) hn.2⟩

include s in
/-- A signed Sylow marking of the actual quotient action proves the missing
ambient normalizer index. The original index-two factor premise remains used. -/
theorem source_residual_normalizer_index_of_signed_coordinates
    (hc : residualClosure H Mc = residual H)
    (e : MulAut (residual H ⧸ pCore 2 (residual H)) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) (he : Function.Injective e)
    (hS : ((T : Subgroup G).subgroupOf Mc).map (e.comp (residualPartnerAction Mc H hc)) =
      Matrix.GeneralLinearGroup.SignedFive.signedSubgroup) :
    (Mc ⊓ normalizer (residual H2 : Set G)).relIndex Mc = 2 := by
  let f := e.comp (residualPartnerAction Mc H hc)
  let S := T.subtype (source_residual_partner_sylow_le s)
  have him : ((T : Subgroup G).subgroupOf Mc).map f = f.range :=
    hS.trans (Matrix.GeneralLinearGroup.SignedFive.range_eq_signed_of_sylow f S hS).symm
  let N := (normalizer (residual H2 : Set G)).subgroupOf Mc
  have hker : f.ker ≤ N := by
    intro x hx
    have hx' : x ∈ (residualPartnerAction Mc H hc).ker := by
      change residualPartnerAction Mc H hc x = 1
      apply he
      exact hx.trans e.map_one.symm
    exact (source_residual_action_kernel_normalizes s hc).2 (mem_map_of_mem Mc.subtype hx')
  rw [inf_relIndex_left]
  change N.index = 2
  rw [index_eq_relIndex_of_image_eq_range f _ N hker him]
  rw [relIndex_subgroupOf (source_residual_partner_sylow_le s)]
  simpa only [inf_relIndex_left] using residual_second_normalizer_index a s.factors s.outside.1.2

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (hc : residualClosure H Mc = residual H)
    (e : MulAut (residual H ⧸ pCore 2 (residual H)) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) (he : Function.Injective e)
    (hS : ((T : Subgroup G).subgroupOf Mc).map (e.comp (residualPartnerAction Mc H hc)) =
      Matrix.GeneralLinearGroup.SignedFive.signedSubgroup)

/-- Construct all residual normalizer geometry from a signed Sylow marking
of its literal quotient action. ResidualSigned supplies this marking from
the original source context. -/
noncomputable def signedResidualNormalizerGeometry :
    NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative :=
  indexedResidualNormalizerGeometry s hc
    (source_residual_normalizer_index_of_signed_coordinates s hc e he hS)

include s hc e he hS in
/-- The signed action criterion supplies the literal second normalizer and C.2.3. -/
theorem signed_residual_secondNormalizer_setup :
    s.critical.endpoint.representative ∈ normalizer (residual H2 : Set G) ∧
      ¬normalizer (residual H2 : Set G) ≤ Mc ∧
      Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
        (normalizer (residual H2 : Set G)) (Mc.pCoreIn 2)
          (Mc ⊓ normalizer (residual H2 : Set G)) ∧
      ((T : Subgroup G) ⊓ normalizer (residual H2 : Set G)).relIndex T = 2 :=
  indexed_residual_secondNormalizer_setup s hc
    (source_residual_normalizer_index_of_signed_coordinates s hc e he hS)

include s hc e he hS in
/-- The same marking supplies the escaping component and its normalized
C.2.7 comparison, preserving the literal second factor throughout. -/
theorem signed_residual_normalized_component_comparison :
    Nonempty (SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2)) ∧
    ∀ j : SourceEscapingComponent Mc (residualClosure H Mc)
      (residual H1) (residual H2) (Mc.pCoreIn 2),
      Input KnownSimple.IsKnownSimple (normalizer (residual H2 : Set G))
        (Mc.pCoreIn 2) (Mc ⊓ normalizer (residual H2 : Set G)) j.J ∧
      ¬Nonempty (NaturalStarRow j.J (Mc.pCoreIn 2)) :=
  indexed_residual_normalized_component_comparison s hc
    (source_residual_normalizer_index_of_signed_coordinates s hc e he hS)
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
