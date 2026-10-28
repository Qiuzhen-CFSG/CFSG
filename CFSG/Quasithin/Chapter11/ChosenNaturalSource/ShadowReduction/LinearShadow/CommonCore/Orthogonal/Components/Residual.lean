module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Inputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Two-generation and residual assembly for the original orthogonal join

Transvections generate SL₂ in characteristic two. Passing through the
literal two-core quotient and lifting over its two-group kernel proves
O^{2′}(L₂)=L₂ and O^{2′}(K)=K. Thus the original join Y already lies in
O^{2′}(G_P), with no generation premise left to the caller.

If the two actual factors are normal in G_P and contain the original
Sylow in their join, then V lies in that join and I≤KV identifies Y with
K∨L₂. This proves relative normality and finishes the odd-index residual
equality. The component recognition and Sylow-order argument must still
supply those two premises in the final source assembly.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, printed p.774.
The odd-index residual here is distinct from K=O²(H).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem generated_by_two_of_core_quotient
    {J : Type*} [Group J] [Finite J] {F : BinaryField}
    (e : (J ⧸ pCore 2 J) ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    primeToResidual 2 J = ⊤ := by
  have hQ : pCore 2 J ≤ primeToResidual 2 J := by
    intro x hx
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := J)) ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  have hr : primeToResidual 2 (J ⧸ pCore 2 J) = ⊤ := by
    apply top_unique
    intro x _
    have hx := Matrix.SL2.map_mem_primeToResidual 2 e.symm.toMonoidHom (e x)
    change e.symm (e x) ∈ primeToResidual 2 (J ⧸ pCore 2 J) at hx
    simpa only [e.symm_apply_apply] using hx
  have hm := map_primeToResidual_of_surjective 2
    (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)
  rw [hr] at hm
  have he := congrArg (fun U => U.comap (QuotientGroup.mk' (pCore 2 J))) hm
  simpa only [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQ, comap_top] using he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}

theorem source_local_generated_by_two (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) : primeToResidual 2 (f.Li 1) = ⊤ :=
  generated_by_two_of_core_quotient (F := S.field) ((SL3.flagLocalCoreEquiv S m f 1).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := S.field.Carrier)).symm)

theorem source_residual_generated_by_two
    (d : OrthogonalInput D S m f H X A h) : primeToResidual 2 (outsideResidual H) = ⊤ :=
  generated_by_two_of_core_quotient (F := d.pair_field) d.pair_natural.quotientEquiv

theorem source_orthogonalJoin_le_oddResidual
    (d : OrthogonalInput D S m f H X A h) :
    orthogonalJoin (f.Li 1) V h ≤
      (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype :=
  orthogonalJoin_le_oddResidual d.source d.conjugator_mem (f.Li 1) d.local_core
    (source_local_generated_by_two S m f)

theorem source_orthogonalJoin_eq_oddResidual_of_normal_sylow
    (d : OrthogonalInput D S m f H X A h)
    (hn : ((orthogonalJoin (f.Li 1) V h).subgroupOf (coreNormalizer V H h)).Normal)
    (hT : (T : Subgroup G) ≤ orthogonalJoin (f.Li 1) V h) :
    orthogonalJoin (f.Li 1) V h =
      (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype :=
  orthogonalJoin_eq_oddResidual d.source d.conjugator_mem (f.Li 1) d.local_core
    (source_local_generated_by_two S m f) hn hT

/-- Once the original Sylow is in the product, its seed supplies the original pair. -/
theorem source_orthogonalJoin_eq_factorJoin
    (d : OrthogonalInput D S m f H X A h)
    (hT : (T : Subgroup G) ≤ outsideResidual H ⊔ f.Li 1) :
    orthogonalJoin (f.Li 1) V h = outsideResidual H ⊔ f.Li 1 := by
  have hk : outsideResidual H ≤ pairGroup V h := by
    rw [← d.pair_residual]
    exact outsideResidual_le _
  apply le_antisymm
  · exact sup_le le_sup_right
      ((pairGroup_le_residual_join_seed d.source d.conjugator_mem).trans
        (sup_le le_sup_left (D.le_sylow.trans hT)))
  · exact sup_le (hk.trans le_sup_right) le_sup_left

/-- Actual relative normality of both factors and Sylow containment finish
    the residual calculation. Component recognition and the Sylow order
    argument must supply these hypotheses in the final source assembly. -/
theorem source_orthogonalJoin_eq_oddResidual_of_normal_factors
    (d : OrthogonalInput D S m f H X A h)
    (hK : ((outsideResidual H).subgroupOf (coreNormalizer V H h)).Normal)
    (hL : ((f.Li 1).subgroupOf (coreNormalizer V H h)).Normal)
    (hT : (T : Subgroup G) ≤ outsideResidual H ⊔ f.Li 1) :
    orthogonalJoin (f.Li 1) V h =
      (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype := by
  have hy := orthogonalJoin_le_coreNormalizer d.source d.conjugator_mem (f.Li 1) d.local_core
  have hk : outsideResidual H ≤ pairGroup V h := by
    rw [← d.pair_residual]
    exact outsideResidual_le _
  have hkn : coreNormalizer V H h ≤ normalizer (outsideResidual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hk.trans (le_sup_right.trans hy))).mp hK
  have hln : coreNormalizer V H h ≤ normalizer (f.Li 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hy)).mp hL
  have he := source_orthogonalJoin_eq_factorJoin d hT
  apply source_orthogonalJoin_eq_oddResidual_of_normal_sylow d
  · apply (normal_subgroupOf_iff_le_normalizer hy).mpr
    rw [he]
    exact (le_inf hkn hln).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · rwa [he]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
