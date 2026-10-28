module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncentralCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionFusionSource

/-!
# Sylow centralizers of the original field involutions

The two fixed-point counts and the original involution-closure theorem show that
C_T(s) is Sylow in C_G(s). This assembles both center cases with every fusion,
fixed-cardinality and local-model premise discharged from the minimal block.
Source: Aschbacher–Smith, 2.4.23(4), printed pp.537–538.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_field_centralizer_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : T) (hs : (s:G) ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(s:G)}:Set G))
      (centralizer ({(s:G)}:Set G)) := by
  by_cases hZ : center (d.block.map d.H.subtype) = ⊥
  · exact source_centerless_field_centralizer_sylow d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
  · exact source_noncenterless_field_centralizer_sylow d hG T hST hsingle hL hM hTM hu c hZ
      (c.involution_fusion_closed d hG T hST hsingle hL hM hTM hu) s hs hs2 hsR
end CFSG.Quasithin.Chapter2.LinearShadows.Single
