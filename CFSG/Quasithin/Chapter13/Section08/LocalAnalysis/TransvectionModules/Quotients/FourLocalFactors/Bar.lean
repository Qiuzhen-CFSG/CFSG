module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Irreducible

/-!
# The bar kernel in Notation 12.2.5(2)

The bar denotes the image in N_G(V)/C_{N_G(V)}(V). For P ≤ N_G(V),
its kernel is C_P(V), not an unspecified normal subgroup or automatically
O₂(P). We identify P/C_P(V) with its actual image in that quotient.

Source: Aschbacher–Smith (1 March 2004), printed p.796, Notation 12.2.5(2),
used in the local module calculation of 13.8.6(4), printed p.948.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

variable {G : Type*} [Group G]

/-- The kernel of the source bar map restricted to P. -/
def barKernel (P V : Subgroup G) : Subgroup P := (centralizer (V : Set G)).subgroupOf P

/-- The map into the actual quotient from Notation 12.2.5(2). -/
def barMap (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    P →* (normalizer (V : Set G) ⧸
      (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G))) :=
  (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf
    (normalizer (V : Set G)))).comp (inclusion hPV)

theorem barMap_ker (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    (barMap P V hPV).ker = barKernel P V := by
  ext p
  exact QuotientGroup.eq_one_iff (inclusion hPV p)

theorem barKernel_normal (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    (barKernel P V).Normal := by
  rw [← barMap_ker P V hPV]
  infer_instance

/-- The intrinsic bar quotient is the actual bar image, with its canonical map. -/
noncomputable def barEquivImage (P V : Subgroup G)
    (hPV : P ≤ normalizer (V : Set G)) :
    letI := barKernel_normal P V hPV
    (P ⧸ barKernel P V) ≃* (barMap P V hPV).range := by
  letI := barKernel_normal P V hPV
  exact (QuotientGroup.quotientMulEquivOfEq (barMap_ker P V hPV).symm).trans
    (QuotientGroup.quotientKerEquivRange (barMap P V hPV))

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
