module
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
/-!
# The reduced commutator is contained in the intrinsic module

For a subnormal two-perfect X, R₂(G) lies in the omega-center of O₂(G).
The commutator therefore lies in V(X,O₂(G)), which A.4.8 places in the
original intrinsic module V(X). In particular, a zero intrinsic module
forces X to centralize R₂(G). No quotient classification is used.
Source: Aschbacher--Smith, A.4.8 and A.4.11, printed pp.59--61.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
theorem reduced_commutator_le_intrinsicModule (X : Subgroup G)
    (hsub : X.IsSubnormal) (hX : IsPPerfect 2 X) :
    ⁅reducedTwoSubgroup G, X⁆ ≤ intrinsicSignalizerModule X := by
  let := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
  have hR : reducedTwoSubgroup G ≤ omegaOneCenterAmbient (pCore 2 G) := by
    intro r hr
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨reducedPSubgroup_le_pCore 2 G hr,
        elemPow_eq_one_of_isElementaryAbelian r hr,
        reducedPSubgroup_le_centralizer_pCore 2 G hr⟩
  have hn : X ≤ normalizer (pCore 2 G : Set G) := le_normalizer_of_normal
  have hcomm : ⁅X, pCore 2 G⁆ ≤ X.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal X (pCore 2 G)
      hsub hX pCore_isPGroup hn).trans (map_mono (commutator_le_left _ _))
  calc
    ⁅reducedTwoSubgroup G,X⁆ ≤ ⁅omegaOneCenterAmbient (pCore 2 G),X⁆ :=
      commutator_mono hR le_rfl
    _ = signalizerModule X (pCore 2 G) := by
      rw [signalizerModule_eq_commutator_omegaCenter,commutator_comm]
    _ ≤ intrinsicSignalizerModule X := signalizerModule_le_intrinsicModule X (pCore 2 G)
      hX hn (pCoreIn_le_of_subnormal 2 hsub) hcomm
end CFSG.Quasithin.ChapterA.Section04
