module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Localization

/-!
# Comparing the actual A.3.18 image with K+

The localized C-component has a quasisimple two-core quotient and
nontrivial image R in KLᵥ/O₃′(KLᵥ). Its two-core is killed by this quotient,
so R is quasisimple. The same intrinsic quotient surjects onto the actual
plus image P. Comparing the two central quotients yields R/Z(R) ≃ P/Z(P),
with an equation on every representative k ∈ K. The kernels need not be
equal; the proof uses their common quasisimple source.

Source: Aschbacher–Smith, A.3.18, pp.51–53, and 13.6.20, p.931.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentSelection Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hr : primeRank 3 K = 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)

/-- Factor the literal local quotient map through O₂(C). -/
noncomputable def localTwoCoreToImage :
    (localComponent K L v ⧸ pCore 2 (localComponent K L v)) →* localImage K L v :=
  twoCoreToThreePrimeImage _
    (source_local_cComponent hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR).subnormal

theorem localTwoCoreToImage_surjective :
    Function.Surjective (localTwoCoreToImage hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR) :=
  twoCoreToThreePrimeImage_surjective _ _

theorem localTwoCoreToImage_mk (k : K) :
    localTwoCoreToImage hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR
      (QuotientGroup.mk' (pCore 2 (localComponent K L v)) ((localComponentEquiv K L v).symm k)) =
      toLocalImage K L v k := rfl

include hG hA36 hA312 hv hK hr hSyl hn hL hz hR in
/-- Quasisimplicity for the actual image used by A.3.18. -/
theorem source_localImage_quasisimple : IsQuasisimple (localImage K L v) := by
  let := (source_local_intrinsic hG hA36 K L T z v hv hK hr).2.2.1
  let := localImage_nontrivial K L v hr
  exact IsQuasisimple.of_surjective
    (localTwoCoreToImage hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR)
    (localTwoCoreToImage_surjective hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR)

/-- The comparison uses the literal local and plus quotient maps. -/
noncomputable def localPlusCentralQuotientEquiv :
    (localImage K L v ⧸ center (localImage K L v)) ≃*
      (plusImage K L T z v hL hz K ⧸ center (plusImage K L T z v hL hz K)) := by
  let := (source_local_intrinsic hG hA36 K L T z v hv hK hr).2.2.1
  let := localImage_nontrivial K L v hr
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  exact IsQuasisimple.imageCentralQuotientEquiv
    (localTwoCoreToImage hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR)
    (localTwoCoreToImage_surjective hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR)
    ((intrinsicTwoCoreToPlus K L T z v hL hz hK hR).comp (localTwoCoreEquiv K L v).toMonoidHom)
    ((intrinsicTwoCoreToPlus_surjective K L T z v hL hz hK hR).comp
      (localTwoCoreEquiv K L v).surjective)

/-- The comparison commutes with both maps from the original K. -/
theorem localPlusCentralQuotientEquiv_mk (k : K) :
    localPlusCentralQuotientEquiv hG hA36 hA312 K L T z v hv hK hr hSyl hn hL hz hR
      (QuotientGroup.mk' (center (localImage K L v)) (toLocalImage K L v k)) =
      QuotientGroup.mk' (center (plusImage K L T z v hL hz K))
        (toPlusImage K L T z v hK.1.1 hL hz k) := by
  let := (source_local_intrinsic hG hA36 K L T z v hv hK hr).2.2.1
  let := localImage_nontrivial K L v hr
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  exact IsQuasisimple.imageCentralQuotientEquiv_mk _ _ _ _
    (QuotientGroup.mk' (pCore 2 (localComponent K L v)) ((localComponentEquiv K L v).symm k))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
