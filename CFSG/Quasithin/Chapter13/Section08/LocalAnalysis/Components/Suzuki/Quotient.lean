module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# The actual Suzuki component image

The source's K* is the image in H/O₂(H). Its comparison with the concrete
Suzuki matrix group goes through `Components.componentStarEquiv`, retaining
the proven kernel O₂(K). The parameter m gives field exponent 2m+1; source
applications require m ≥ 1.

This is quotient transport for Aschbacher–Smith 13.8.16, printed pp.952–953
(combined manuscript of 1 March 2004), not an assertion that a Suzuki
component occurs or that its occurrence has been excluded.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki
variable {G : Type*} [Group G] [Finite G]

/-- An intrinsic Suzuki identification induces the corresponding identification
of the literal component image in H*. -/
noncomputable def starModelEquiv (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (m : ℕ)
    (e : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :
    Source.starImage H K ≃* SuzukiMatrixGroup m :=
  (componentStarEquiv H K hKH hK).symm.trans e

/-- The two identifications agree on every element of the intrinsic quotient. -/
theorem starModelEquiv_componentStarEquiv (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (m : ℕ)
    (e : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) (k : K ⧸ pCore 2 K) :
    starModelEquiv H K hKH hK m e (componentStarEquiv H K hKH hK k) = e k := by
  simp [starModelEquiv]

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki
