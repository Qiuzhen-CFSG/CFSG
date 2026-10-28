module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncenterlessFusionSource

/-!
# Involution fusion in the original single linear block

The centerless and noncenterless source arguments together show that every
involution of R conjugate into T remains in R. All fixed-point, local-module
and fusion inputs are discharged from the original minimal-block setup.
This is Aschbacher–Smith, 2.4.21(2), printed pp.535–536, in the literal form
used by the quotient and transfer arguments of 2.4.22–24.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem CyclicTorusSetup.involution_fusion_closed
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) :
    ∀ r t : T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) →
      (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  intro r t hr2 hr hrt
  by_cases hZ : center (d.block.map d.H.subtype) = ⊥
  · exact source_centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hunique c hZ
      r t hr ((Subgroup.orderOf_coe r).trans hr2) t.property hrt
  · exact source_noncenterless_involution_fusion_contained d hG T hST hsingle hL hM hTM hunique c hZ
      r hr (by simpa only [(Subgroup.orderOf_coe r).trans hr2] using
        pow_orderOf_eq_one (r : G))
      t t.property hrt
end CFSG.Quasithin.Chapter2.LinearShadows.Single
