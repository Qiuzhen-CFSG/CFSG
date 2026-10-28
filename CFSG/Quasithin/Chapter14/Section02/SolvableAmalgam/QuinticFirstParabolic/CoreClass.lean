module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.CoreNoncentral
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.KernelIntersections
public import CFSG.Quasithin.Chapter14.Section02.ProperSpan
public import Theory.GroupTheory.NormalizerAction.OmegaCenterCentralizer
public import Theory.GroupTheory.ClassTwoConjugateCores

/-!
# An unconditional class lower bound for the original quintic core

Let Q=O₂(H), B=O₂(X), X=YT and Z=Ω₁Z(T). The original crossing-core
index gives Q≰B and QB=T. Each nontrivial T-normal subgroup contains Z.
The already proved nonabelian intersections Q∩Qˣ therefore rule out class
two: the class-two conjugate-core lemma would make Q centralize
⟨Zˣ : x∈X⟩, which contains the original plane V. But C_X(V)=B,
contradicting Q≰B.

Thus [Q,Q,Q]≠1 and Q has class at least three under the unchanged source
hypotheses, before any core-order bound. `IntrinsicCore` uses this result
for its exact third-commutator and class computations. The unconditional
upper bound on |Q| remains with qt-e-quintic-first-parabolic.

Source: Aschbacher--Smith F.9.7, p.321;14.2.6 and14.2.20--21,
pp.982,988--989. Conjugates and cores retain their ambient embeddings.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The third lower-central term of the original quintic core is nontrivial,
without an order or endpoint-identification premise. -/
theorem source_core_third_commutator_ne_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    ⁅⁅H.pCoreIn 2,H.pCoreIn 2⁆,H.pCoreIn 2⁆ ≠ ⊥ := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let S := (T : Subgroup G)
  let Q := H.pCoreIn 2
  let B := X.pCoreIn 2
  let Z := centralInvolutions T
  have hTH : S ≤ H := hH.1.1.2
  have hTX : S ≤ X := le_sup_right
  have hQT : Q ≤ S := by
    exact (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq
      (map_subgroupOf_eq_of_le hTH)
  have hBT : B ≤ S := by
    exact (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq
      (map_subgroupOf_eq_of_le hTX)
  have hSQ : S ≤ normalizer (Q : Set G) := hTH.trans (H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hXB : X ≤ normalizer (B : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  obtain ⟨hB,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hBi : B.relIndex S = 2 := by
    let P := T.subtype hTX
    have hm := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal P)
    rw [SymmetricThreeTwoCore.sylow_index_three eX P, SymmetricThreeTwoCore.core_index eX] at hm
    have hi' : (pCore 2 X).relIndex (P : Subgroup X) = 2 := by omega
    have hmap : (P : Subgroup X).map X.subtype = S := map_subgroupOf_eq_of_le hTX
    change (X.pCoreIn 2).relIndex S = 2
    rw [←hmap,pCoreIn,relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hi'
  have hiK : (Q ⊓ B).relIndex Q = 2 :=
    source_quintic_crossing_core_index hG T hempty hM hu hmany hcard e H hH hi
  have hQB : ¬ Q ≤ B := by
    intro hh
    have hiOne : (Q ⊓ B).relIndex Q = 1 := relIndex_eq_one.mpr (le_inf le_rfl hh)
    omega
  have hsplit : Q ⊔ B = S := by
    have hjoin : Q ⊔ B ≤ S := sup_le hQT hBT
    have hm := relIndex_mul_relIndex B (Q ⊔ B) S le_sup_right hjoin
    rw [hBi] at hm
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hp | hp
    · exact le_antisymm hjoin (relIndex_eq_one.mp hp.2)
    · exact (hQB (le_sup_left.trans (relIndex_eq_one.mp hp.2))).elim
  have hdetect (D : Subgroup G) (hDS : D ≤ S)
      (hSD : S ≤ normalizer (D : Set G)) (hne : D ≠ ⊥) : Z ≤ D := by
    let DS := D.subgroupOf S
    let : DS.Normal := normal_subgroupOf_of_le_normalizer hSD
    have hn : DS ≠ ⊥ := by
      intro he
      apply hne
      have hh := congrArg (map S.subtype) he
      simpa only [DS,map_subgroupOf_eq_of_le hDS,Subgroup.map_bot] using hh
    have hz : Nat.card (omega₁ (center S) (p := 2)) = 2 := by
      have hh := plane_centralInvolutions_card T M hM.1.2 hcard e
      change Nat.card (((omega₁ (center S) (p := 2)).map (center S).subtype).map S.subtype) = 2 at hh
      simpa only [card_map_of_injective S.subtype_injective,
        card_map_of_injective (center S).subtype_injective] using hh
    have hh := omega_center_le_normal_of_card_eq_prime T.isPGroup' hz DS hn
    exact (map_mono (f := S.subtype) hh).trans_eq (map_subgroupOf_eq_of_le hDS)
  intro hclass
  have hc : Q ≤ centralizer (conjugateSpanBy Z X : Set G) :=
    class_two_centralizes_span_of_nonabelian_crossings X S B Q Z hBT hSQ hXB hsplit
      hdetect (fun x hx => source_core_crossing_intersection_nonabelian
        hG T hempty hM hu hmany hcard e H hH hi x hx) hclass
  have hV : localModule T M ≤ conjugateSpanBy Z X := by
    rw [source_plane_module_residual_span hG T hempty hM hu hmany hcard e]
    exact conjugateSpanBy_mono le_rfl le_sup_left
  apply hQB
  rw [show B = X ⊓ centralizer (localModule T M : Set G) from hB]
  exact le_inf (hQT.trans hTX) (hc.trans (centralizer_le hV))


/-- The actual quintic core has nilpotency class at least three before any order bound. -/
theorem source_core_nilpotencyClass_lower
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    3 ≤ Group.nilpotencyClass (H.pCoreIn 2) := by
  let Q := H.pCoreIn 2
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 H).isNilpotent
  have hn := source_core_third_commutator_ne_bot hG T hempty hM hu hmany hcard e H hH hi
  have hnot : ¬ Group.nilpotencyClass Q ≤ 2 := by
    intro hc
    have he : (⊤ : Subgroup Q).lowerCentralSeries 2 = ⊥ :=
      Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc
    have hm := congrArg (fun A : Subgroup Q => A.map Q.subtype) he
    rw [map_lowerCentralSeries,← MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] at hm
    exact hn hm
  change 3 ≤ Group.nilpotencyClass Q
  omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
