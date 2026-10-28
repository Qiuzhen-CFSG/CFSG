module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Defs
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Geometry
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.GroupTheory.SolvableResidual

/-!
# Native actions on the geometric trio sections

The pair-generated term has dimension nine in the actual cocode and its
quotient has dimension two. The trio stabilizer preserves both this term
and the fixed space of its intrinsic two-core. Their restricted and quotient
actions are defined here directly from the native cocode representation.
The residual is `Subgroup.solvableResidual` of the intrinsic stabilizer,
mapped into M24; no ambient normality is imposed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.6,
printed p.401. The printed middle section `V₉/V` is corrected to `V₉/V₃`.
The three-dimensional fixed-space calculation, its containment in the pair
space, the chief factors and the full action and tensor identifications
remain separate proof obligations.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

/-- Restriction of the actual cocode action to the native trio stabilizer. -/
def trioRepresentation (T : Trio) : Representation (ZMod 2) (trioStabilizer T) Cocode :=
  cocodeRepresentation.comp (trioStabilizer T).subtype

lemma finrank_trioPairSpace (T : Trio) :
    Module.finrank (ZMod 2) (trioPairSpace T) = 9 :=
  TrioCalculation.finrank_pairSpace T

lemma finrank_trioPairQuotient (T : Trio) :
    Module.finrank (ZMod 2) (Cocode ⧸ trioPairSpace T) = 2 := by
  have h := (trioPairSpace T).finrank_quotient_add_finrank
  rw [finrank_trioPairSpace, finrank_cocode] at h
  omega

lemma trioPairSpace_strict (T : Trio) :
    (⊥ : Submodule (ZMod 2) Cocode) < trioPairSpace T ∧ trioPairSpace T < ⊤ := by
  have h := finrank_trioPairSpace T
  constructor
  · refine bot_lt_iff_ne_bot.mpr ?_
    intro hz
    rw [hz, finrank_bot] at h
    omega
  · refine lt_top_iff_ne_top.mpr ?_
    intro ht
    rw [ht, finrank_top, finrank_cocode] at h
    omega

lemma trioPairSpace_invariant (T : Trio) (g : trioStabilizer T)
    {v : Cocode} (hv : v ∈ trioPairSpace T) : trioRepresentation T g v ∈ trioPairSpace T :=
  TrioCalculation.pairSpace_invariant T g.val g.property hv

/-- The middle term with its actual stabilizer action. -/
def trioPairSubrepresentation (T : Trio) : Subrepresentation (trioRepresentation T) where
  toSubmodule := trioPairSpace T
  apply_mem_toSubmodule g _ hv := trioPairSpace_invariant T g hv

lemma trioFixedSpace_eq_intrinsic (T : Trio) :
    trioFixedSpace T = fixedSpace (trioRepresentation T) (pCore 2 (trioStabilizer T)) :=
  (fixedSpace_comp_map cocodeRepresentation (trioStabilizer T).subtype
    (pCore 2 (trioStabilizer T))).symm

lemma trioFixedSpace_invariant (T : Trio) (g : trioStabilizer T)
    {v : Cocode} (hv : v ∈ trioFixedSpace T) : trioRepresentation T g v ∈ trioFixedSpace T := by
  rw [trioFixedSpace_eq_intrinsic] at hv ⊢
  exact (fixedSpace_stable_of_normal (trioRepresentation T) (pCore 2 (trioStabilizer T))
    (Subgroup.mem_top g) v).2 hv

/-- The fixed space is invariant because the two-core is normal in its own stabilizer. -/
def trioFixedSubrepresentation (T : Trio) : Subrepresentation (trioRepresentation T) where
  toSubmodule := trioFixedSpace T
  apply_mem_toSubmodule g _ hv := trioFixedSpace_invariant T g hv

/-- The top factor carries the action induced from the actual cocode quotient. -/
def trioTopRepresentation (T : Trio) :
    Representation (ZMod 2) (trioStabilizer T) (Cocode ⧸ trioPairSpace T) :=
  (trioPairSubrepresentation T).quotientRepresentation

/-- The restriction of the fixed space to the geometric middle term. The
source inclusion `trioFixedSpace T ≤ trioPairSpace T` remains a theorem obligation. -/
def trioSectionKernel (T : Trio) : Subrepresentation (trioPairSubrepresentation T).toRepresentation where
  toSubmodule := (trioFixedSpace T).comap (trioPairSpace T).subtype
  apply_mem_toSubmodule g _ hv := trioFixedSpace_invariant T g hv

/-- The literal middle section. Once the source inclusion is established,
this is `V₉/V₃`, correcting the printed `V₉/V`. -/
abbrev TrioSection (T : Trio) :=
  (trioPairSpace T) ⧸ (trioFixedSpace T).comap (trioPairSpace T).subtype

def trioSectionRepresentation (T : Trio) :
    Representation (ZMod 2) (trioStabilizer T) (TrioSection T) :=
  (trioSectionKernel T).quotientRepresentation

/-- The perfect residual is intrinsic to the stabilizer before mapping to M24. -/
def trioResidual (T : Trio) : Subgroup M24 :=
  (Subgroup.solvableResidual (trioStabilizer T)).map (trioStabilizer T).subtype

lemma trioResidual_le_stabilizer (T : Trio) : trioResidual T ≤ trioStabilizer T := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

lemma trioKernel_le_stabilizer (T : Trio) : trioKernel T ≤ trioStabilizer T := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
