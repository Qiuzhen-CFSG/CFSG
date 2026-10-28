module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Inputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients

/-!
# The two local components in the common-core normalizer

The original outside residual is a C-component of H, and H contains the
original Sylow. The genuine local-family restriction therefore places it
in L(G_P,T). The independently marked flag residual has an actual PSL₂
core quotient, which supplies its own local-family membership. Known-simple
containment and the Sylow orbit bound give unique normal containing
C-components, with every normality assertion relative to G_P.

The outside condition separates K from L₂, and containment of P in both
factors separates their images in the literal Y/P. We also locate P normally
in T and compute its order from the original natural marking. Equality with
the containing components and the structure of T/P are still required;
this module does not assert their recognition or a product marking.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, printed p.774;
Definition 1.2.3, 1.2.4 and A.3.12 for local-family containment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)

include d

theorem source_residual_le_pair : outsideResidual H ≤ pairGroup V h := by
  rw [← d.pair_residual]
  exact outsideResidual_le _

/-- H preserves P because P is the characteristic two-core of its residual. -/
theorem source_outside_le_coreNormalizer : H ≤ coreNormalizer V H h := by
  rw [coreNormalizer, ← d.residual_core]
  exact (outsideResidual_normalized H).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem source_residual_le_coreNormalizer : outsideResidual H ≤ coreNormalizer V H h :=
  (source_residual_le_pair d).trans
    (pairGroup_normalizes_pairCore d.source d.conjugator_mem)

theorem source_residual_mem_local : outsideResidual H ∈ Chapter1.L G T :=
  Chapter1.mem_L_of_cComponent d.source.outside.1.1.1
    ⟨T.subtype d.source.outside.1.1.2,
      map_subgroupOf_eq_of_le d.source.outside.1.1.2⟩
    (outsideResidual_le H) d.residual_component

theorem source_residual_mem_normalizer_local :
    (outsideResidual H).subgroupOf (coreNormalizer V H h) ∈
      Chapter1.L (coreNormalizer V H h)
        ((T : Subgroup G).subgroupOf (coreNormalizer V H h)) :=
  (Chapter1.mem_LIn_iff_subgroupOf (sylow_le_coreNormalizer f d.local_core)
    (source_residual_le_coreNormalizer d)).mp
      ⟨source_residual_le_coreNormalizer d, source_residual_mem_local d⟩

theorem source_residual_not_le_seed_normalizer :
    ¬ outsideResidual H ≤ normalizer (L : Set G) := by
  intro hk
  apply d.source.outside.1.2
  rw [← outsideResidual_sup_sylow T H d.source.outside.1.1.2]
  exact sup_le hk D.sylow_normalizes_component

theorem source_local_mem_normalizer_local :
    (f.Li 1).subgroupOf (coreNormalizer V H h) ∈
      Chapter1.L (coreNormalizer V H h)
        ((T : Subgroup G).subgroupOf (coreNormalizer V H h)) := by
  have hle : f.Li 1 ≤ coreNormalizer V H h := le_sup_left.trans
    (orthogonalJoin_le_coreNormalizer d.source d.conjugator_mem (f.Li 1) d.local_core)
  apply (Chapter1.mem_LIn_iff_subgroupOf (sylow_le_coreNormalizer f d.local_core) hle).mp
  refine ⟨hle, Components.flag_mem_local_of_model D S f 1 ?_⟩
  exact ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq,
    ⟨SL3.flagLocalCoreEquiv S m f 1⟩⟩

theorem source_residual_ne_local : outsideResidual H ≠ f.Li 1 := by
  intro he
  apply source_residual_not_le_seed_normalizer d
  rw [he]
  exact ((localResidual_le _).trans inf_le_left).trans L.le_normalizer

theorem source_residual_containing_component :
    ∃ Kplus : Subgroup G, Source.NormalComponentIn (coreNormalizer V H h) Kplus ∧
      outsideResidual H ≤ Kplus ∧
      ∀ J : Subgroup G, Source.ComponentIn (coreNormalizer V H h) J →
        outsideResidual H ≤ J → J = Kplus := by
  apply Components.exists_unique_normal_component
    (S.source.simpleQTKE.twoLocal_sqtk
      (coreNormalizer_twoLocal f d.conjugator_mem d.axis_eq_plane))
    ⟨T.subtype (sylow_le_coreNormalizer f d.local_core),
      map_subgroupOf_eq_of_le (sylow_le_coreNormalizer f d.local_core)⟩
    (source_residual_le_coreNormalizer d) (source_residual_mem_local d)
  exact d.source.outside.1.1.2.trans (outsideResidual_normalized H)

theorem source_local_containing_component :
    ∃ Lplus : Subgroup G, Source.NormalComponentIn (coreNormalizer V H h) Lplus ∧
      f.Li 1 ≤ Lplus ∧
      ∀ J : Subgroup G, Source.ComponentIn (coreNormalizer V H h) J →
        f.Li 1 ≤ J → J = Lplus := by
  have hle : f.Li 1 ≤ coreNormalizer V H h := le_sup_left.trans
    (orthogonalJoin_le_coreNormalizer d.source d.conjugator_mem (f.Li 1) d.local_core)
  have hlocal : f.Li 1 ∈ Chapter1.L G T :=
    ((Chapter1.mem_LIn_iff_subgroupOf (sylow_le_coreNormalizer f d.local_core) hle).mpr
      (source_local_mem_normalizer_local d)).2
  exact Components.exists_unique_normal_component
    (S.source.simpleQTKE.twoLocal_sqtk
      (coreNormalizer_twoLocal f d.conjugator_mem d.axis_eq_plane))
    ⟨T.subtype (sylow_le_coreNormalizer f d.local_core),
      map_subgroupOf_eq_of_le (sylow_le_coreNormalizer f d.local_core)⟩
    hle hlocal (f.sylow_normalizes_Li 1)

theorem source_pairCore_le_sylow : pairCore V H h ≤ (T : Subgroup G) := by
  have hc := pCoreIn_le_sylow H (T.subtype d.source.outside.1.1.2)
  change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hc
  rw [map_subgroupOf_eq_of_le d.source.outside.1.1.2] at hc
  exact (pairCore_le_core d.conjugator_mem).trans hc

theorem source_pairCore_normal_sylow :
    ((pairCore V H h).subgroupOf (T : Subgroup G)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (source_pairCore_le_sylow d)).mpr
    (sylow_le_coreNormalizer f d.local_core)

theorem source_pairCore_card : Nat.card (pairCore V H h) = (2 ^ S.field.degree) ^ 4 := by
  have hc := d.pair_natural.card
  simpa only [d.pair_degree, d.pair_multiplicity] using hc

/-- The common core lies in each of the two actual source factors. -/
theorem source_pairCore_le_factors :
    pairCore V H h ≤ outsideResidual H ∧ pairCore V H h ≤ f.Li 1 := by
  constructor
  · rw [← d.residual_core]
    exact pCoreIn_le 2 _
  · rw [← d.local_core]
    exact pCoreIn_le 2 _

/-- The two factors remain distinct in the literal quotient Y/P. -/
theorem source_quotient_factors_distinct :
    let Y := orthogonalJoin (f.Li 1) V h
    let P := (pairCore V H h).subgroupOf Y
    let := pairCore_normal_in_orthogonalJoin d.source d.conjugator_mem (f.Li 1) d.local_core
    ((outsideResidual H).subgroupOf Y).map (QuotientGroup.mk' P) ≠
      ((f.Li 1).subgroupOf Y).map (QuotientGroup.mk' P) := by
  dsimp only
  let Y := orthogonalJoin (f.Li 1) V h
  let P := (pairCore V H h).subgroupOf Y
  let := pairCore_normal_in_orthogonalJoin d.source d.conjugator_mem (f.Li 1) d.local_core
  intro he
  have hK : outsideResidual H ≤ Y := (source_residual_le_pair d).trans le_sup_right
  have hL : f.Li 1 ≤ Y := le_sup_left
  have he' := congrArg (fun Q => Q.comap (QuotientGroup.mk' P)) he
  have hPK : (QuotientGroup.mk' P).ker ≤ (outsideResidual H).subgroupOf Y := by
    rw [QuotientGroup.ker_mk']
    exact comap_mono (source_pairCore_le_factors d).1
  have hPL : (QuotientGroup.mk' P).ker ≤ (f.Li 1).subgroupOf Y := by
    rw [QuotientGroup.ker_mk']
    exact comap_mono (source_pairCore_le_factors d).2
  rw [comap_map_eq_self hPK, comap_map_eq_self hPL] at he'
  have he'' := congrArg (map Y.subtype) he'
  rw [map_subgroupOf_eq_of_le hK, map_subgroupOf_eq_of_le hL] at he''
  exact source_residual_ne_local d he''

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
