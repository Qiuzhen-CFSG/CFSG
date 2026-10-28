module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.Relative
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.SourceDichotomy

/-!
# The literal D application of C.2.7(1–2)

The original fixed component is normal inside Gᵤ. Its genuine pushing-up
setup, characteristic two and quasisimple quotient therefore produce the
kernel bounds, reduced omega-center module and actual offenders. Every term
uses the original Gᵤ, Lᵤ, Rᵤ and H∩Gᵤ; no identification with U is made.
The eight marked alternatives of C.2.7(3) remain a separate source family.

Source: Aschbacher--Smith 14.7.68(2), pp.1071–1072, applying C.2.7.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_local_clauses
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    KernelConclusion Lu (d.fixedCore u) ∧ OffenderConclusion Lu (d.fixedCore u) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.kernel_offender_of_normal_input
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
