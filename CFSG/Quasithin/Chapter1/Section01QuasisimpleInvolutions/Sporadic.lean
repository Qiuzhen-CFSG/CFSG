module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M12.Properties.SylowCentralizing
public import Theory.Mathieu.M22.Properties.SylowPointwise.Innerness
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySylowFixers
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ElementarySylowFixers

/-!
# The available sporadic cases of 1.1.5(3)(f)

The five Mathieu groups, J₂, J₄, and HS have proved intrinsic innerness
calculations. Apply them to the original quotient action, then lift innerness
and use odd-core inversion to identify the center with the two-core.
Every conclusion is the canonical row (f), with the original automorphism
and original Sylow subgroup. No multiplier premise is required.

For HS, the already checked graph-centralizer certificate places each
pointwise Sylow fixer inside the actual carrier. Sylow conjugacy transports
this conclusion to the specified Sylow subgroup. This uses the same intrinsic
certificate as `HS.ElementarySylowFixers`, retaining its ATLAS attribution.
Held and Rudvalis still require their independently owned outer-action inputs.

Source: Aschbacher--Smith, 1.1.5(3)(f), printed pp.501--503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
open Sporadic.Mathieu
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The M11 central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_m11 (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* M11) : ModelAction115 L α := by
  apply d.sporadic_of_quotient_inner .m11 (by intro h; cases h) e
  obtain ⟨g, hg⟩ := automorphism_inner_of_equiv_m11 (MulEquiv.refl M11)
    (MulAut.centralQuotientAction e α)
  exact ⟨g, hg.symm⟩

/-- The M12 central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_m12 (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* M12) : ModelAction115 L α := by
  apply d.sporadic_of_quotient_inner .m12 (by intro h; cases h) e
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  obtain ⟨g, hg⟩ := m12_automorphism_inner_of_fixes_sylow _ Q hQ
  exact ⟨g, hg.symm⟩

/-- The M22 central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_m22 (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* M22) : ModelAction115 L α := by
  apply d.sporadic_of_quotient_inner .m22 (by intro h; cases h) e
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  obtain ⟨g, hg⟩ := M22SylowPointwise.automorphism_inner_of_fixes_sylow _ Q hQ
  exact ⟨g, hg.symm⟩

/-- The M23 central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_m23 (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* M23) : ModelAction115 L α := by
  exact d.sporadic_of_quotient_inner .m23 (by intro h; cases h) e (m23_conj_surjective _)

/-- The M24 central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_m24 (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* M24) : ModelAction115 L α := by
  exact d.sporadic_of_quotient_inner .m24 (by intro h; cases h) e
    (M24OuterRestriction.conj_surjective _)

/-- The J2 central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_j2 (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Sporadic.LeechRelated.J2.Carrier) : ModelAction115 L α := by
  apply d.sporadic_of_quotient_inner .j2 (by intro h; cases h) e
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  obtain ⟨g, hg⟩ := Sporadic.LeechRelated.J2.automorphism_inner_of_fixes_sylow Q _ hQ
  exact ⟨g, hg.symm⟩

/-- The J4 central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_j4 (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Janko4.Model) : ModelAction115 L α := by
  exact d.sporadic_of_quotient_inner .j4 (by intro h; cases h) e (Janko4.AdequateLocal.conj_surjective _)

open Sporadic.LeechRelated.HS in
private theorem hs_base_fixer_inner (r : MulAut Carrier)
    (hfix : ∀ x ∈ EvenLocalCandidates.subgroup, r x = x) :
    ∃ g, r = MulAut.conj g := by
  open EvenLocalCandidates ElementarySylowFixers in
  obtain ⟨p, rfl⟩ := normalizer_surjective_of_pointStabilizer_map pointStabilizer_map r
  have hc : ∀ i, Commute p.val (ElementarySylowFixers.Certificate.gen i) := by
    intro i
    have hx := hfix (EvenLocalCandidates.sylowGenerator i) (subset_closure ⟨i, rfl⟩)
    have he := congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100))) hx
    change p.val * (EvenLocalCandidates.sylowGenerator i : Equiv.Perm (Fin 100)) * p.val⁻¹ =
      (EvenLocalCandidates.sylowGenerator i : Equiv.Perm (Fin 100)) at he
    rw [← ElementarySylowFixers.Certificate.gen_eq] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hp := ElementarySylowFixers.Certificate.centralizer_mem p.val hc
    (NormalizerIndex.normalizer_le_graphGroup p.property)
  refine ⟨⟨p.val, hp⟩, ?_⟩
  ext x
  rfl

open Sporadic.LeechRelated.HS in
private theorem hs_fixer_inner (r : MulAut Carrier) (S : Sylow 2 Carrier)
    (hfix : ∀ x ∈ S, r x = x) : ∃ g, r = MulAut.conj g := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier BlockNormalizer.baseSylow S
  let e := MulAut.conj g
  apply (MulAut.congr_inner_iff e.symm r).mp
  apply hs_base_fixer_inner
  intro x hx
  have hmem : e x ∈ S := by
    rw [← hg]
    change e x ∈ EvenLocalCandidates.subgroup.map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom hx
  change e.symm (r (e x)) = x
  rw [hfix _ hmem, e.symm_apply_apply]

/-- The HS central-quotient case of source row (f), with the original action. -/
theorem MarkedInvolution.modelAction_hs (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Sporadic.LeechRelated.HS.Carrier) : ModelAction115 L α := by
  apply d.sporadic_of_quotient_inner .hs (by intro h; cases h) e
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  obtain ⟨g, hg⟩ := hs_fixer_inner _ Q hQ
  exact ⟨g, hg.symm⟩

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
