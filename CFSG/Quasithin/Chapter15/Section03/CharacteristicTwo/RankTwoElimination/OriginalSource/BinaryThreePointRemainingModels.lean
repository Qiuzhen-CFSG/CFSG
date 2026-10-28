module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSimple
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSmallModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointRankTwoModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointRankGap
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSporadicModels

/-!
# Remaining simple carriers above the original binary-three component

The full-Sylow local calculations exclude every Theorem C characteristic-two
rank-two carrier, every Bender carrier, and J₁. The ambient cubic rank and
normality also exclude the odd quadratic PSL₂ carrier, and hence all odd
linear rows. Alternating degrees five and six, M₁₁, M₁₂, M₂₂ and J₂ are
excluded by the actual quotient and full Sylow placement. The remaining
alternatives retain both signs in the odd ternary family and the six
unexcluded sporadic carriers.

These are carrier exclusions inside the original ambient problem, not its
final contradiction. The remaining proper embeddings still require the
original opposed-core geometry.

Source: Aschbacher--Smith A.3.6, A.3.12 and 15.3.23,
printed pp.43--48 and 1128--1129.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.Section02.LocalModels

/-- Actual simple carriers left by the proved full-Sylow binary-three
embedding exclusions. Each alternative retains its group isomorphism. -/
def BinaryThreeRemainingSimpleCarrier (X : Type*) [Group X] : Prop :=
  (∃ n : ℕ, (n = 7 ∨ n = 8) ∧ IsAlternating X n) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsPSLSign X unitary 3 p) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL X n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty (X ≃* name.Carrier))

/-- The original smaller binary section removes the small, rank-one and
characteristic-two rank-two rows from the full simple carrier catalogue. -/
theorem binary_three_remaining_simple_carrier
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {B K : Subgroup X} [K.Normal]
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hK : K.IsCComponent) (hBK : B < K)
    (hSB : (S : Subgroup X) ≤ normalizer (B : Set X))
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (h3 : 2 ≤ primeRank 3 X) (hN : primeRank 3 (normalizer (B : Set X)) ≤ 1)
    (hm : TheoremCModel K) : BinaryThreeRemainingSimpleCarrier K := by
  cases hm with
  | alternating n hn he =>
    have hd : 7 ∣ Nat.card K := by
      apply (show 7 ∣ Nat.card (B ⧸ pCore 2 B) from ?_).trans
        ((card_quotient_dvd_card _).trans (card_dvd_of_le hBK.le))
      rw [Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv,Matrix.PSL3Two.card_SL]
      decide
    have hn7 : n = 7 ∨ n = 8 := by
      obtain ⟨a⟩ := he
      rw [Nat.card_congr a.toEquiv] at hd
      obtain ⟨hlo,hhi⟩ := hn
      interval_cases n
      · rw [nat_card_alternatingGroup] at hd
        norm_num [Nat.factorial] at hd
      · rw [nat_card_alternatingGroup] at hd
        norm_num [Nat.factorial] at hd
      · exact .inl rfl
      · exact .inr rfl
    exact .inl ⟨n,hn7,he⟩
  | linear_odd p d hp ho hd _ he =>
    exact (binary_three_point_not_odd_linear S hB hK hBK e hN h3 hp ho hd he).elim
  | three_odd p hp ho unitary he =>
    exact .inr (.inl ⟨p,hp,ho,unitary,he⟩)
  | rank_one he => exact (binary_three_point_not_bender S hB hK hBK he).elim
  | rank_two he => exact (hBK.ne (binary_three_eq_of_rank_two_model S hB hK hBK.le e he)).elim
  | binary_linear n hn he => exact .inr (.inr (.inl ⟨n,hn,he⟩))
  | sporadic name hn he =>
    exact .inr (.inr (.inr ⟨name,
      binary_three_point_sporadic_model_remaining S hB hK hBK hSB e name hn he,he⟩))
  | janko_one he => exact (binary_three_point_not_jankoOne hBK.le e he.some).elim

open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual original large-distance point with the surviving carrier
families. No carrier-exclusion callback or MS93 earlier premise remains. -/
theorem binary_three_large_distance_point_remaining_models
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
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q ∧
          IsSimpleGroup (K.map q) ∧ BinaryThreeRemainingSimpleCarrier (K.map q) := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel⟩ :=
    binary_three_large_distance_point_simple
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let : (K.map q).Normal := hKnq
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
  have hremaining := binary_three_remaining_simple_carrier
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) hB hKq hBKq hSB he hr.ge hn hmodel
  exact ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hremaining⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
