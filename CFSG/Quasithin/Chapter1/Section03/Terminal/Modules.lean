module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.Definitions
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Comparison
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The internal-module deduction in Lemma 1.3.9(2)

Set K = ⟨L^T⟩ and U = T ∩ K. Relative normality in LT proves U is
Sylow in K. Since T normalizes X, the exact hypotheses of A.4.10 hold
for X ≤ K and U. Its module bound is already the requested V(X,S) ≤ V(K).

To descend nontriviality to L, suppose V(L) = 1. Subnormality of L in K
and A.4.8 imply that L centralizes Ω₁(Z(O₂(K))). This omega-center is
T-invariant, so every T-conjugate of L centralizes it and V(K) = 1.

The only unproved inputs are the universally quantified earlier source
implications 1.1.4(6) and A.4.10. Their owners are qt-1-01 and qt-a-04;
qt-1-03 retains their discharge under the global simple QTKE hypotheses.
No maximality or terminal module containment is included in these inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
A.4.8–10, pp.59–60, and 1.3.9, p.514.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter1.Terminal
open ChapterA.Section04
variable {G : Type*} [Group G]

/-- The full universal earlier Lemma A.4.10, with its actual signalizer and module outputs.
This proposition is an explicit theorem parameter, to be supplied by the A.4 owner. -/
def SourceA410 (G : Type*) [Group G] : Prop :=
  ∀ X Y U : Subgroup G, X ≤ Y → IsSignalizerType X → IsSignalizerType Y →
    U ≤ normalizer (Y : Set G) → IsSylowIn 2 U (Y ⊔ U) →
    (Y ⊔ U).pCoreIn 2 ≤ U ⊓ normalizer (X : Set G) →
    IsSylowIn 2 (U ⊓ normalizer (X : Set G)) ((Y ⊔ U) ⊓ normalizer (X : Set G)) →
    IsMaximalTwoSignalizer X ((Y ⊔ U) ⊓ normalizer (X : Set G))
      (twoSectionCentralizer X U) ∧
    signalizerModule X (twoSectionCentralizer X U) ≤ signalizerModule Y ((Y ⊔ U).pCoreIn 2) ∧
    (IsFaithfulSignalizerType X → IsFaithfulSignalizerType Y)

private theorem perfect_twoPerfect [Finite G] [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hn hp
  let := hn
  let := hp.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)


private theorem signalizerType_of_subnormal [Finite G] {B H : Subgroup G}
    [Group.IsPerfect B] (hB : B ≠ ⊥) (hBH : B ≤ H)
    (hsub : (B.subgroupOf H).IsSubnormal) (hH : H ∈ He G) : IsSignalizerType B := by
  refine ⟨hB, perfect_twoPerfect, generalizedFitting_eq_pCore_of_selfCentralizing 2 ?_⟩
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hBH)).mp
    (subnormal_core_selfCentralizing (mem_He_iff.mp hH) _ hsub)

/-- Restrict the ambient Sylow subgroup to a subgroup it normalizes. -/
theorem sylow_inf_of_normalizes [Finite G] (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    IsSylowIn 2 ((T : Subgroup G) ⊓ K) K := by
  let H := K ⊔ (T : Subgroup G)
  have hKH : K ≤ H := le_sup_left
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hTK)
  obtain ⟨S, hS⟩ := (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)).exists_subgroupOf_eq_of_normal
    (K.subgroupOf H)
  let e := subgroupOfEquivOfLe hKH
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup (K.subgroupOf H)).map e.toMonoidHom).map K.subtype = _
  ext g
  constructor
  · rintro ⟨k, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨by rw [hS] at hs; exact hs, (e s).property⟩
  · rintro ⟨ht, hk⟩
    exact ⟨⟨g, hk⟩, ⟨⟨⟨g, hKH hk⟩, hk⟩, by rw [hS]; exact ht, rfl⟩, rfl⟩

/-- Both L and its T-conjugate orbit belong to X, using the exact universal 1.1.4(6). -/
theorem local_component_and_orbit_signalizerType [Finite G] (T : Sylow 2 G)
    (h114 : HOver G (T : Set G) ⊆ He G) {B : Subgroup G} (hB : B ∈ L G T) :
    IsSignalizerType B ∧ IsSignalizerType (componentOrbit B T) := by
  let := mem_L_isPerfect hB
  have hne : B ≠ ⊥ := by
    intro hb
    apply hB.1.ne_bot
    rw [hb, bot_subgroupOf]
  have hH : B ⊔ (T : Subgroup G) ∈ He G := h114 ⟨hB.2.2, show (T : Subgroup G) ≤ B ⊔ (T : Subgroup G) from le_sup_right⟩
  refine ⟨signalizerType_of_subnormal hne le_sup_left hB.1.subnormal hH, ?_⟩
  let : Group.IsPerfect (componentOrbit B (T : Subgroup G)) := isPerfect_iSup_conjugates B T
  exact signalizerType_of_subnormal
    (fun he => hne (le_bot_iff.mp (he ▸ le_componentOrbit B T)))
    (componentOrbit_le_sup B T) (componentOrbit_normal_subgroupOf_sup B T).isSubnormal hH

/-- Nontriviality of the orbit module descends to its local component by A.4.8. -/
theorem intrinsicModule_ne_bot_of_orbit [Finite G] {B T : Subgroup G}
    (hB : B ∈ L G T)
    (hne : intrinsicSignalizerModule (componentOrbit B T) ≠ ⊥) :
    intrinsicSignalizerModule B ≠ ⊥ := by
  let K := componentOrbit B T
  let := mem_L_isPerfect hB
  have hp : IsPPerfect 2 B := perfect_twoPerfect
  have hBK : B ≤ K := le_componentOrbit B T
  have hs : (B.subgroupOf K).IsSubnormal :=
    (hB.1.subgroupOf_of_le hBK (componentOrbit_le_sup B T)).subnormal
  have hBQ : B ≤ normalizer (K.pCoreIn 2 : Set G) :=
    hBK.trans (K.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore K))
  have hsig : IsTwoSignalizer B K (K.pCoreIn 2) :=
    (isTwoSignalizer_iff _ _ _).mpr ⟨pCoreIn_le _ _, isPGroup_pCoreIn _ _, hBQ⟩
  have hcomm := signalizer_commutator_le_pCore B K (K.pCoreIn 2) hBK hs hp hsig
  have hdetect := signalizerModule_ne_bot_iff_intrinsic B (K.pCoreIn 2) hp
    (isPGroup_pCoreIn _ _) hBQ (pCoreAmbient_mono_of_isSubnormalIn B K 2 hBK hs) hcomm
  intro hzero
  have hz : signalizerModule B (K.pCoreIn 2) = ⊥ := by
    by_contra hn
    exact (hdetect.mp hn) hzero
  have hTQ : T ≤ normalizer (omegaOneCenterAmbient (K.pCoreIn 2) : Set G) :=
    (le_normalizer_componentOrbit B T).trans
      ((normalizer_le_normalizer_intrinsicCore K).trans (normalizer_le_normalizer_omegaCenter _))
  have hc : K ≤ centralizer (omegaOneCenterAmbient (K.pCoreIn 2) : Set G) :=
    iSup_conjugates_le_centralizer B T _ hTQ
      ((signalizerModule_eq_commutator_omegaCenter B _).symm.trans hz)
  apply hne
  change signalizerModule K (K.pCoreIn 2) = ⊥
  rw [signalizerModule_eq_commutator_omegaCenter]
  exact commutator_eq_bot_iff_le_centralizer.mpr hc

/-- The full deduction of 1.3.9(2) from the exact universal earlier source implications.
The source assembly must discharge h114 and hA410; this is not an unconditional
proof of the numbered source theorem. -/
theorem lemma_1_3_9_two_of_A_4_10 [Finite G] (T : Sylow 2 G)
    (h114 : HOver G (T : Set G) ⊆ He G) (hA410 : SourceA410 G)
    {X B : Subgroup G} (hX : X ∈ XiF G T) (hB : B ∈ L G T)
    (hXB : X ≤ componentOrbit B T) :
    signalizerModule X (twoSectionCentralizer X ((T : Subgroup G) ⊓ componentOrbit B T)) ≤
        intrinsicSignalizerModule (componentOrbit B T) ∧
      B ∈ MainForward.faithfulLocalComponents T := by
  let K := componentOrbit B (T : Subgroup G)
  let U := (T : Subgroup G) ⊓ K
  obtain ⟨hBX, hKX⟩ := local_component_and_orbit_signalizerType T h114 hB
  have hUK : U ≤ K := inf_le_right
  have hUN : U ≤ normalizer (X : Set G) := inf_le_left.trans hX.1.invariant
  have hKU : K ⊔ U = K := sup_eq_left.mpr hUK
  have hSyl : IsSylowIn 2 U K := sylow_inf_of_normalizes T K (le_normalizer_componentOrbit B T)
  have hcore : K.pCoreIn 2 ≤ U := by
    obtain ⟨S, hS⟩ := hSyl
    exact hS ▸ pCoreIn_le_sylow K S
  have hUSyl : IsSylowIn 2 (U ⊓ normalizer (X : Set G)) (K ⊓ normalizer (X : Set G)) := by
    rw [inf_of_le_left hUN]
    exact hSyl.restrict (le_inf hUK hUN) inf_le_left
  have ha := hA410 X K U hXB hX.2.1 hKX (hUK.trans K.le_normalizer)
    (hKU.symm ▸ hSyl) (hKU.symm ▸ le_inf hcore (hcore.trans hUN)) (hKU.symm ▸ hUSyl)
  have hKf := ha.2.2 hX.2
  refine ⟨?_, (mem_L_iff_localComponents T B).mp hB, hBX, intrinsicModule_ne_bot_of_orbit hB hKf.2⟩
  change signalizerModule X (twoSectionCentralizer X U) ≤ signalizerModule K (K.pCoreIn 2)
  simpa only [hKU] using ha.2.1

end CFSG.Quasithin.Chapter1.Terminal
end
