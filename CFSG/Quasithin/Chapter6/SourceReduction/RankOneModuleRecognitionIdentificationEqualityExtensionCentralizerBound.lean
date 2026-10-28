module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionPermutationCore
public import Theory.GroupTheory.IndexTwoCentralizerFixedCard

/-!
# The centralizer order bound in the equality extension

The canonical P has four-group image in M/Q≃S₅, while the actual Sylow
image has order eight. Thus PQ has index two in T. The elementary group
D=C_H(K) centralizes PQ and satisfies C_D(T)=⟨z⟩. The fixed-point bound
for an index-two action gives |D|≤|⟨z⟩|²=4. Since D contains the marked
involution, its order is two or four. Both alternatives remain present;
the source transfer argument must still exclude the four-group case.

Source: Aschbacher–Smith, proof of 6.2.13, printed p.687.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- P Q has index two in the actual Sylow group, as its image is a four
inside the eight-group of the marked S₅ quotient. -/
theorem LocalAnalysis.equality_core_local_join_index
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ((equalityCore L R z).map (centralizer ({z} : Set G)).subtype ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
  let H := centralizer ({z} : Set G)
  let P := (equalityCore L R z).map H.subtype
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hPT : P ≤ (T : Subgroup G) := equalityCore_le_sylow hTH
  have hPM := hPT.trans h611.sylow_le
  have hQT : Q ≤ (T : Subgroup G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [← equality_sylow_centralizer_eq_core h611 hnatural]
    exact inf_le_left
  have hQM := hQT.trans h611.sylow_le
  obtain ⟨f, hf, hker, _, _, _, h4, _⟩ :=
    A.equality_core_permutation_image h611 hnatural hz horder hTH hbranch
  let j : equalityCore L R z →* M := equalityCoreToMaximal hTH h611.sylow_le
  have hj : j.range = P.subgroupOf M := by
    ext m
    constructor
    · rintro ⟨p, rfl⟩
      change (j p : G) ∈ P
      rw [show (j p : G) = (p.val : G) from equalityCoreToMaximal_coe hTH h611.sylow_le p]
      exact mem_map_of_mem H.subtype p.property
    · rintro ⟨p, hp, he⟩
      refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
      exact (equalityCoreToMaximal_coe hTH h611.sylow_le ⟨p, hp⟩).trans he
  have hP4 : Nat.card ((P.subgroupOf M).map f) = 4 := by
    change Nat.card (f.comp j).range = 4 at h4
    rwa [MonoidHom.range_comp, hj] at h4
  let TM := (T : Subgroup G).subgroupOf M
  let S := (T.subtype h611.sylow_le).mapSurjective hf
  have hT8 : Nat.card (TM.map f) = 8 := by
    change Nat.card S = 8
    exact (Nat.card_congr (S.equiv
      Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.standardSylow).toEquiv).trans
      Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.eight_card
  have hi : ((P.subgroupOf M).map f).relIndex (TM.map f) = 2 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 5)))
      ((P.subgroupOf M).map f) (TM.map f) bot_le (map_mono (subgroupOf_mono M hPT))
    rw [relIndex_bot_left, relIndex_bot_left, hP4, hT8] at hc
    omega
  rw [relIndex_map_map, hker, sup_eq_left.mpr (subgroupOf_mono M hQT)] at hi
  have hm := (relIndex_map_map_of_injective
    ((P.subgroupOf M) ⊔ (Q.subgroupOf M)) TM M.subtype_injective).trans hi
  rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hPM,
    map_subgroupOf_eq_of_le hQM, map_subgroupOf_eq_of_le h611.sylow_le] at hm

/-- The canonical centralizer has order two or four. Its action factors
through T/PQ of order two, and its fixed subgroup is the central line. -/
theorem LocalAnalysis.equality_centralizer_card
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nat.card (equalityCentralizer L R z) = 2 ∨ Nat.card (equalityCentralizer L R z) = 4 := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let P := (equalityCore L R z).map H.subtype
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := equalityCentralizer L R z
  let := A.equality_centralizer_elementary h611 hnatural hz horder hTH hbranch
  let := A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  have hHD : H ≤ normalizer (D : Set G) := by
    change H ≤ normalizer ((centralizer (K : Set H)).map H.subtype : Set G)
    have hh := (centralizer (K : Set H)).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hDP : D ≤ centralizer (P : Set G) := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨p, hp, rfl⟩
    exact congrArg Subtype.val (hd p (pCoreIn_le 2 _ hp))
  have hDQ : D ≤ centralizer (Q : Set G) :=
    (A.equality_centralizer_le_local_core h611 hnatural hz hTH).trans Q.le_centralizer
  have hDPQ : D ≤ centralizer ((P ⊔ Q : Subgroup G) : Set G) := by
    exact le_centralizer_iff.mpr
      (sup_le (le_centralizer_iff.mp hDP) (le_centralizer_iff.mp hDQ))
  have hbound := card_le_centralizer_card_sq_of_relIndex_two D (P ⊔ Q) (T : Subgroup G)
    (hTH.trans hHD) hDPQ
    (A.equality_core_local_join_index h611 hnatural hz horder hTH hbranch)
  have hfixed : Nat.card ((centralizer (T : Set G)).subgroupOf D) = 2 := by
    calc
      Nat.card ((centralizer (T : Set G)).subgroupOf D) =
          Nat.card (((centralizer (T : Set G)).subgroupOf D).map D.subtype) :=
        (card_map_of_injective D.subtype_injective).symm
      _ = 2 := by
        rw [subgroupOf_map_subtype, inf_comm,
          A.equality_centralizer_sylow_fixed h611 hnatural hz horder hTH hbranch,
          Nat.card_zpowers, horder]
  change Nat.card D ≤ Nat.card ((centralizer (T : Set G)).subgroupOf D) ^ 2 at hbound
  rw [hfixed] at hbound
  have hlower := card_le_of_le (equality_line_le_centralizer z L R)
  rw [Nat.card_zpowers, horder] at hlower
  change 2 ≤ Nat.card D at hlower
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 3 ≤ k by omega)
    omega
  change Nat.card D = 2 ∨ Nat.card D = 4
  interval_cases k
  · have hh : Nat.card D = 1 := hk
    omega
  · exact Or.inl hk
  · exact Or.inr hk

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
