module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
public import Theory.GroupTheory.ReducedNormal.FiveBorel

/-!
# Symmetric-five fixation of the original Sylow omega-center

The marked quotient of the moved subgroup makes the relative residual Borel
fix omega. Transport through the literal inclusion of LT identifies that
Borel with N_L(T∩L). To use this with an arbitrary original reduced W,
reselect the conjugate span of Ω₁Z(T) under L: B.2.14 proves its reducedness,
and noncentrality supplies another instance of the same universal Input.
Thus containment of omega is constructed rather than imposed on W.

Source: Aschbacher–Smith 5.1.13, printed p.637, the symmetric-five row.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

/-- The original left Borel fixes omega in the genuine symmetric-five row.
The containing-module premise is supplied below by the actual omega-span. -/
theorem Input.borel_fixes_omega_of_five_section
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ W)
    (hf : let M := L ⊔ (T : Subgroup G)
      let U := W.subgroupOf M
      letI := h.reduced_internal.normal
      letI := h.reduced_internal.elementary
      let V := ⁅U,pResidual 2 M⁆
      ∃ p : M →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
        ∃ hk : p.ker = centralizer (V : Set M),
        ∃ f : Additive V →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
          Function.Surjective f ∧
          (∀ g v, f (NormalElementaryQuotient.representation V p hp hk g v) =
            BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
          f.ker = fixedSpace (NormalElementaryQuotient.representation V p hp hk)
            ((pResidual 2 M).map p)) :
    localBorel T L ≤ omegaCentralizer T := by
  let M := L ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let U := W.subgroupOf M
  let R := pResidual 2 M
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  have hPm : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hZm : (omegaOneCenterAmbient (P : Subgroup M)).map M.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,hPm]
  have hZU : omegaOneCenterAmbient (P : Subgroup M) ≤ U := by
    intro z hz
    exact hZ (hZm ▸ mem_map_of_mem M.subtype hz)
  obtain ⟨p,hp,hk,f,hs,he,hfk⟩ := hf
  have hc := five_borel_fixes_omega P U R hZU p hp hk
    (ChapterC.SymmetricFive.source_residual_image p hp) f hs he hfk
  have hR : R = L.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left)]
    exact h.local_residual_eq
  intro g hg z hz
  let g' : M := ⟨g,mem_sup_left hg.1⟩
  have hgR : g' ∈ R := by rw [hR]; exact hg.1
  let r : R := ⟨g',hgR⟩
  have hr : r ∈ normalizer ((P : Subgroup M).subgroupOf R : Set R) := by
    apply mem_normalizer_iff.mpr
    intro x
    have hxL : (x.val : G) ∈ L := by
      exact hR.le x.property
    have hconjL : g * (x.val : G) * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hg.1 hxL) (L.inv_mem hg.1)
    have hh := mem_normalizer_iff.mp hg.2 (x.val : G)
    change ((x.val : G) ∈ (T : Subgroup G) ↔ g * (x.val : G) * g⁻¹ ∈ (T : Subgroup G))
    simpa only [mem_inf,hxL,hconjL,and_true] using hh
  have hgr := hc (mem_map_of_mem R.subtype hr)
  obtain ⟨z',hz',hz'e⟩ := hZm.ge hz
  have hh := congrArg M.subtype (hgr z' hz')
  change (z' : G) * g = g * (z' : G) at hh
  change (z' : G) = z at hz'e
  rwa [hz'e] at hh

/-- The source permits reselecting the actual omega-span, whose reducedness
is B.2.14. This retains all original group and outside hypotheses. -/
theorem Input.omega_span_input
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hn : ¬ L ≤ omegaCentralizer T) :
    Input KnownSimple.IsKnownSimple T L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  have hr := LocalOmega.span_reduced T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  exact { h with
    reduced := ⟨hu.2.trans le_sup_right,hu.1,hr.normal,hr.quotient_pCore_eq_bot⟩
    noncentral := LocalOmega.module_ne_bot T L hn }

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
