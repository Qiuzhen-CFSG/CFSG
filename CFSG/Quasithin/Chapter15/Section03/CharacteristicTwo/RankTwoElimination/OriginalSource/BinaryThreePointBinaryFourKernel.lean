module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiniteModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreJoin
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original intrinsic four lies in the binary-carrier point kernel

Restrict the original full image Sylow to the normal containing carrier.
The literal smaller subgroup is normalized by that Sylow and its order is
divisible by seven. The finite flag calculation makes its two-core class
at most two in PSL₄(2) and PSL₅(2). The original intrinsic four is the third
commutator of Q, so its image under the original point quotient vanishes.

This preserves C=C_G(z), N=O₂(C), q and the actual embedded B and K.
It neither asserts that Q lies in N nor assumes that K normalizes Q.
Source: Aschbacher--Smith 15.3.23, printed pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93

/-- Full-Sylow normalization inside the actual normal binary carrier kills
the third commutator of the smaller component core. -/
theorem binary_three_point_binary_intrinsicFour_eq_bot
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {B K : Subgroup X} [K.Normal]
    (hBK : B ≤ K) (hSB : (S : Subgroup X) ≤ normalizer (B : Set X))
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2) :
    intrinsicFour B = ⊥ := by
  obtain ⟨F,_,_,hF,⟨a₀⟩⟩ := hm
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let a := (a₀.trans (Atlas.fieldEquivPSL n f)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n))
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal K
  let D := B.subgroupOf K
  have hTD : (T : Subgroup K) ≤ normalizer (D : Set K) := by
    rw [hT,← subgroupOf_normalizer_eq hBK]
    exact fun _ hx => hSB hx
  let U := T.mapSurjective (f := a.toMonoidHom) a.surjective
  have hUD : (U : Subgroup _) ≤ normalizer (D.map a.toMonoidHom : Set (BinaryLinear.OuterCyclic.LinearGroup n)) :=
    (map_mono hTD).trans (D.le_normalizer_map a.toMonoidHom)
  have h7B : 7 ∣ Nat.card B := by
    apply (show 7 ∣ Nat.card (B ⧸ pCore 2 B) from ?_).trans (card_quotient_dvd_card _)
    rw [Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv, Matrix.PSL3Two.card_SL]
    decide
  have h7D : 7 ∣ Nat.card (D.map a.toMonoidHom) := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective D a.toMonoidHom a.injective).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv]
    exact h7B
  have hc := BinaryLinear.SevenFlagCore.normalized_twoCore_third_eq_bot hn U
    (D.map a.toMonoidHom) hUD h7D
  have hcD : ⁅⁅D.pCoreIn 2,D.pCoreIn 2⁆,D.pCoreIn 2⁆ = ⊥ := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_commutator,map_commutator,map_pCoreIn_of_injective 2 D _ a.injective,
      Subgroup.map_bot]
    exact hc
  have hcB : ⁅⁅B.pCoreIn 2,B.pCoreIn 2⁆,B.pCoreIn 2⁆ = ⊥ := by
    have hh := congrArg (fun V : Subgroup K => V.map K.subtype) hcD
    simpa only [map_commutator,map_pCoreIn_of_injective 2 D _ K.subtype_injective,
      D,map_subgroupOf_eq_of_le hBK,Subgroup.map_bot] using hh
  apply eq_bot_iff.mpr
  exact (commutator_mono (commutator_mono (commutatorCore_le B) (commutatorCore_le B))
    (commutatorCore_le B)).trans hcB.le

private theorem intrinsicFour_map {A H : Type*} [Group A] [Group H] [Finite A] [Finite H]
    (f : A →* H) (hk : IsPGroup 2 f.ker) (L : Subgroup A) :
    (intrinsicFour L).map f = intrinsicFour (L.map f) := by
  simp only [intrinsicFour,LinearThree.commutatorCore,map_commutator,
    map_pCoreIn_of_ker_isPGroup f hk]

variable {G : Type*} [Group G] [Finite G]

/-- The literal intrinsic four of the original source lies in the literal
point kernel for either remaining binary carrier. -/
theorem binary_three_source_binary_four_kernel
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2) :
    intrinsicFour c.L ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp b.component_normal)
  have hPB : (P : Subgroup C) ≤ normalizer (c.L.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hLC]
    intro x hx
    apply hSL
    exact hP ▸ mem_map_of_mem C.subtype hx
  have hSB := (map_mono (f := q) hPB).trans ((c.L.subgroupOf C).le_normalizer_map q)
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let A := c.L.subgroupOf C
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hq.comap_subtype
  let a := subgroupOfEquivOfLe hLC
  let eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2) :=
    ((q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e)
  have hzero := binary_three_point_binary_intrinsicFour_eq_bot
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) hBK hSB eB hn hm
  have hQ : LinearThree.commutatorCore c.L ≤ C :=
    (commutatorCore_le c.L).trans ((c.L.pCoreIn_le 2).trans hLC)
  have hQQ : ⁅LinearThree.commutatorCore c.L,LinearThree.commutatorCore c.L⁆ ≤
      LinearThree.commutatorCore c.L := (Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl)
  have hHC : intrinsicFour c.L ≤ C :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le (hQQ.trans hQ) hQ)
  have hsubker : IsPGroup 2 C.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff C.subtype).mpr C.subtype_injective]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hi : intrinsicFour (c.L.subgroupOf C) = (intrinsicFour c.L).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hHC,intrinsicFour_map C.subtype hsubker,
      map_subgroupOf_eq_of_le hLC]
  have hkill : ((intrinsicFour c.L).subgroupOf C).map q = ⊥ := by
    rw [←hi,intrinsicFour_map q hq]
    exact hzero
  have hle : (intrinsicFour c.L).subgroupOf C ≤ pCore 2 C := by
    have hh : (intrinsicFour c.L).subgroupOf C ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hkill
    simpa only [q,QuotientGroup.ker_mk'] using hh
  rw [←map_subgroupOf_eq_of_le hHC]
  exact map_mono hle

/-- The original finite-carrier packet retains the same point and all its
placements, with the intrinsic-four kernel inclusion in both binary rows. -/
theorem binary_three_large_distance_point_binary_four_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      primeRank 3 (C ⧸ pCore 2 C) = 2 ∧
      primeRank 3 (normalizer (B : Set (C ⧸ pCore 2 C))) ≤ 1 ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) : Subgroup _) ≤
          normalizer (B : Set (C ⧸ pCore 2 C)) ∧
        Nonempty (((B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
          Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C)) ⧸
          pCore 2 (B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
            Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C))) ≃*
          PSL(3,ZMod 2)) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q ∧
          IsSimpleGroup (K.map q) ∧ BinaryThreeFiniteSimpleCarrier (K.map q) ∧
          (∀ n : ℕ, (n = 4 ∨ n = 5) → ClassicalGroup.IsPSL (K.map q) n 2 →
            intrinsicFour c.L ≤ C.pCoreIn 2) := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel⟩ :=
    binary_three_large_distance_point_finite_models
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  refine ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,?_⟩
  intro n hn hm
  let := hKnq
  exact binary_three_source_binary_four_kernel d c e b z hLS P hP
    (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) hBKq.le hn hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
