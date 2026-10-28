module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
/-!
# The source barred actor and its restricted centralizer kernel

Notation 12.2.5(2), printed p.796 of Aschbacher–Smith's combined manuscript
of 1 March 2004, takes bars in MV/C_MV(V), with MV = N_G(V). The first
isomorphism theorem identifies the image of any P ≤ MV with
P/C_P(V). In particular P = LT gives precisely the actor used in 13.8.6(5).
The comparison retains the quotient-map formula and asserts only relative
normality. A coordinate marking of L₁T remains a separate obligation.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed
variable {G : Type*} [Group G]

/-- The restricted kernel of the source barred action on V. -/
def actorKernel (P V : Subgroup G) : Subgroup P := (centralizer (V : Set G)).subgroupOf P

/-- The source ambient barred group, using MV = N_G(V) from 12.2.5(2). -/
abbrev Bar (V : Subgroup G) :=
  normalizer (V : Set G) ⧸ (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G))

/-- Restriction of the actual MV-centralizer quotient to P. -/
def toBar (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) : P →* Bar V :=
  (QuotientGroup.mk' _).comp (inclusion hPV)

theorem toBar_kernel (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    (toBar P V hPV).ker = actorKernel P V := by
  ext p
  exact QuotientGroup.eq_one_iff (inclusion hPV p)

/-- Normality is in P, not in the ambient group. -/
theorem actorKernel_normal (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    (actorKernel P V).Normal := by
  rw [← toBar_kernel P V hPV]
  infer_instance

/-- The quotient of P by its restricted kernel is precisely its source bar image. -/
noncomputable def actorEquivBarImage (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    letI := actorKernel_normal P V hPV
    (P ⧸ actorKernel P V) ≃* (toBar P V hPV).range := by
  letI := actorKernel_normal P V hPV
  exact (QuotientGroup.quotientMulEquivOfEq (toBar_kernel P V hPV).symm).trans
    (QuotientGroup.quotientKerEquivRange (toBar P V hPV))

/-- The image comparison commutes with the original quotient maps. -/
theorem actorEquivBarImage_mk (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) (p : P) :
    letI := actorKernel_normal P V hPV
    ((actorEquivBarImage P V hPV (QuotientGroup.mk' _ p)) : Bar V) = toBar P V hPV p := by
  rfl

theorem actorKernel_map (P V : Subgroup G) :
    (actorKernel P V).map P.subtype = centralizer (V : Set G) ⊓ P :=
  subgroupOf_map_subtype _ _

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed

end
