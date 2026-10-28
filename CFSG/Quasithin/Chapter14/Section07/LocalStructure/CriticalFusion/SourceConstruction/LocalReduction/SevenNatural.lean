module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.PlaneCentralizerSpan
public import Theory.Representation.BinaryConjugationSection.SevenPlaneGeneration

/-!
# Excluding the seven-letter natural local section

When the original point two-core moves the flag plane, its normal closure
has the actual S₃ quotient and plane-centralizer kernel. Quasithin rank
therefore bounds the plane centralizer's three-rank by one. On a proposed
seven-letter natural section, this bound forces a triangle seed plane.
Its point stabilizers generate the whole section, contradicting the proper
plane-normalizer span of the original local.

The general local theorem retains point-core movement explicitly. The
application to the original point normalizer discharges movement in the
normal-point branch and retains only the same-G,T guarded earlier inputs.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
14.7.4(2–3), printed p.1043, and 14.7.37(3), printed pp.1059–1060.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter12.Section09.NaturalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The moving point core generates a normal closure with the actual S₃ quotient
and plane-centralizer kernel, as in 14.7.4(2). -/
theorem planeCoreClosure_quotient_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥) :
    (planeCoreClosure F).pCoreIn 2 = planeCoreClosure F ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((planeCoreClosure F) ⧸ pCore 2 (planeCoreClosure F)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.chosen.elementary
  let P := F.P L
  let R := planeCoreClosure F
  let f := F.binaryPermutationAction (by decide) L h.chosen.normalizes
  have hf : Function.Surjective f := F.binaryPermutationAction_surjective (by decide)
    L h.chosen.normalizes (h.full_LT_action_at structural)
  have hk : f.ker = pCore 2 P :=
    (F.binaryPermutationAction_ker (by decide) L h.chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L h.chosen.normalizes
        (h.full_LT_action_at structural) (h.centralizer_LT_at structural))
  have hcore : P.pCoreIn 2 = P ⊓ centralizer (F.Vi 2 : Set G) :=
    (F.binary_parabolic_core (by decide) L h.chosen.normalizes
      (h.full_LT_action_at structural) (h.centralizer_LT_at structural)).1.symm
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hh hx
    exact hy
  have hout : ¬ F.H.pCoreIn 2 ≤ P.pCoreIn 2 := by
    intro hh
    apply hm
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hh.trans (hcore.le.trans inf_le_right))
  have hgen : R ⊔ P.pCoreIn 2 = P := by
    rw [show R = conjugateSpanBy (F.H.pCoreIn 2) P from planeCoreClosure_eq_parabolic_span h F]
    exact (core_hyperplane_and_generation P (F.H.pCoreIn 2)
      (hQT.trans (F.binary_sylow_le_P L)) (isPGroup_pCoreIn 2 F.H) hout e).2
  have hRP : R ≤ P := planeCoreClosure_le_parabolic h F
  let j := inclusion hRP
  have hs : R.subgroupOf P ⊔ pCore 2 P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRP,←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have him : (R.subgroupOf P).map f = ⊤ := by
    have hh := congrArg (map f) hs
    have hzero : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [Subgroup.map_sup,←hk,hzero,sup_bot_eq,map_top_of_surjective _ hf] at hh
    exact hh
  have hj : Function.Surjective (f.comp j) := by
    intro x
    obtain ⟨r,hr,he⟩ := (show x ∈ (R.subgroupOf P).map f by rw [him]; trivial)
    exact ⟨⟨r,hr⟩,he⟩
  have hkj : IsPGroup 2 (f.comp j).ker := by
    rw [←MonoidHom.comap_ker,hk]
    exact pCore_isPGroup.comap_of_injective j (inclusion_injective hRP)
  have hrk := ker_eq_twoCore_of_surjective_perm_three (f.comp j) hj hkj
  refine ⟨?_,⟨(QuotientGroup.quotientMulEquivOfEq hrk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (f.comp j) hj)⟩⟩
  change (pCore 2 R).map R.subtype = _
  rw [←hrk]
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    refine ⟨r.property,?_⟩
    have hk' : j r ∈ f.ker := hr
    have hh : (r : G) ∈ P.pCoreIn 2 := mem_map_of_mem P.subtype (hk ▸ hk')
    exact (hcore ▸ hh).2
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change f ⟨x,hRP hx⟩ = 1
    have hh : x ∈ P.pCoreIn 2 := hcore.symm ▸ ⟨hRP hx,hc⟩
    obtain ⟨a,ha,he⟩ := hh
    have ha' : a = ⟨x,hRP hx⟩ := Subtype.ext he
    rw [←ha']
    exact (show a ∈ f.ker from hk.symm ▸ ha)

/-- The three-rank bound in 14.7.4(3), with plane movement explicit. -/
theorem plane_centralizer_three_rank_le_one_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥) :
    primeRank 3 (centralizer (F.Vi 2 : Set G)) ≤ 1 := by
  let := h.chosen.elementary
  let I := planeCoreClosure F
  let C := centralizer (F.Vi 2 : Set G)
  have hIG : I ≤ F.Gi 2 := (planeCoreClosure_le_parabolic h F).trans
    (F.P_le_G₂ (by decide) L h.chosen.normalizes)
  have hCG : C ≤ F.Gi 2 := Subgroup.centralizer_le_normalizer _
  have hn := (normal_subgroupOf_iff_le_normalizer hIG).mp (planeCoreClosure_normal h F)
  obtain ⟨hcore,⟨e⟩⟩ := planeCoreClosure_quotient_at h structural hm
  have hIC : IsPGroup 2 (I ⊓ C : Subgroup G) := hcore ▸ isPGroup_pCoreIn 2 I
  have hsum := primeRank_add_le_of_normalizes_of_twoGroup_intersection
    (p := 3) (by decide) I C
    (hIG.trans (normalizer_le_normalizer_centralizer (F.Vi 2))) (hCG.trans hn) hIC
  have hnon : F.Vi 2 ≠ ⊥ := by
    intro he
    have hc := F.card 2 (by decide)
    simp [he] at hc
  have htwoLocal : IsTwoLocal (F.Gi 2) :=
    ⟨F.Vi 2,hnon,F.binaryPlane_elementary.isPGroup,rfl⟩
  have hr : primeRank 3 (F.Gi 2) ≤ 2 :=
    (CFSG.Quasithin.isQuasithin_iff_twoLocal.mp h.source.simpleQTKE.quasithin)
      _ htwoLocal 3 Nat.prime_three (by decide)
  have hup := hsum.trans ((Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion (sup_le hIG hCG)) (inclusion_injective _)).trans hr)
  have hpos : 1 ≤ primeRank 3 I := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup,
      primeRank_congr 3 e]
    let t : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    have ht3 : t ^ 3 = 1 := by decide
    have ht : orderOf t = 3 := orderOf_eq_prime ht3 (by decide)
    let : IsElementaryAbelian 3 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht3
    exact IsElementaryAbelian.primeRank_ge_of_card (zpowers t) (by
      simpa only [Nat.card_zpowers,pow_one] using ht)
  change primeRank 3 C ≤ 1
  omega
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction


namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The seven-letter exclusion in 14.7.37(3), on the literal local section
and actual star quotient, retaining plane movement as an earlier premise. -/
theorem local_seven_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (e : HStar I ≃* Equiv.Perm (Fin 7))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1)
      (BinaryPermutation.SevenParabolic.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))))) : False := by
  let := h.chosen.elementary
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 π.ker := by
    change IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hplane : (F.Vi 1).relIndex (F.Vi 2) = 2 := by
    have hh := ((F.Vi 1).subgroupOf (F.Vi 2)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.monotone (by decide : 1 ≤ 2))).toEquiv,hp] at hh
    have hc : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 (by decide)
    change 2 * (F.Vi 1).relIndex (F.Vi 2) = Nat.card (F.Vi 2) at hh
    omega
  have hseed : (F.Vi 1).relIndex V = 4 := by
    have hh := ((F.Vi 1).subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv,hp] at hh
    have hc : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    change 2 * (F.Vi 1).relIndex V = Nat.card V at hh
    omega
  have hgen := Representation.BinaryConjugationSection.seven_plane_normalizer_generates π c hπ hk V (F.Vi 2) (F.Li L 1)
    (le_conjugateSpanBy V I) (F.le_seed 2) (F.monotone (by decide : 1 ≤ 2))
    hp hplane hseed
    (hI.2.1.trans (normalizer_le_centralizer_of_card_two _ hp))
    (F.Li_one_le_of_mem_Hz hI)
    ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
    (isPPerfect_embedded_pResidual 2 _) (seed_commutator h F).symm
    (plane_centralizer_three_rank_le_one_at h structural hm)
  exact (local_plane_normalizer_span_lt_at h structural hm I hI).ne hgen

/-- Guarded application at the original point normalizer: point normality
supplies movement, and the actual seven-letter natural section is excluded. -/
theorem original_seven_natural_impossible_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (e : HStar F.H ≃* Equiv.Perm (Fin 7))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      (BinaryPermutation.SevenParabolic.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) : False :=
  local_seven_natural_impossible_at h (structural hmany)
    (plane_moved_of_point_normal_at h (structural hmany) hn) F.H
    (h.point_mem_Hz_at F (previous hmany)) e c
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
