module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointRemainingModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointJoinQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointOddTernary

/-!
# Finite remaining carriers at the original binary-three point

The literal original LS quotient has order168. It survives the actual
point quotient as the quotient of B joined with the full image Sylow.
Restriction to the containing component preserves divisibility by168.
The odd ternary models instead force the actual smaller residual SL₂(7),
whose normalizing full-Sylow join has quotient order not dividing168.

Thus only the indicated finite alternating, binary-linear and sporadic
carriers remain. Their proper embeddings are still source obligations;
this theorem does not complete original15.3.23 or assert a universal MS
classification.

Source: Aschbacher--Smith A.3.21 and15.3.23,
printed pp.55--56 and1128--1129.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.Section02.LocalModels

/-- The finite list of actual simple carriers left by the original source
placement and the proved local-component calculations. -/
def BinaryThreeFiniteSimpleCarrier (X : Type*) [Group X] : Prop :=
  (∃ n : ℕ, (n = 7 ∨ n = 8) ∧ IsAlternating X n) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL X n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty (X ≃* name.Carrier))

/-- The preserved original full-Sylow join excludes the infinite odd
ternary family from the same actual containing component. -/
theorem binary_three_finite_simple_carrier
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (hSB : (S : Subgroup X) ≤ normalizer (B : Set X))
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hjoin : Nonempty (((B ⊔ (S : Subgroup X) : Subgroup X) ⧸
      pCore 2 (B ⊔ (S : Subgroup X) : Subgroup X)) ≃* PSL(3,ZMod 2)))
    (hm : BinaryThreeRemainingSimpleCarrier K) : BinaryThreeFiniteSimpleCarrier K := by
  rcases hm with ha | ho | hl | hs
  · exact .inl ha
  · obtain ⟨p,hp,hop,unitary,hmodel⟩ := ho
    have hsmall : Nat.card ((B ⊔ (S : Subgroup X) : Subgroup X) ⧸
        pCore 2 (B ⊔ (S : Subgroup X) : Subgroup X)) ∣ 168 := by
      rw [Nat.card_congr (hjoin.some.trans Matrix.PSL3Two.equiv.symm).toEquiv,
        Matrix.PSL3Two.card_SL]
    exact (binary_three_point_not_odd_ternary S hB hK hBK hSB e hsmall hp hop unitary
      (.inl hmodel)).elim
  · exact .inr (.inl hl)
  · exact .inr (.inr hs)

open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual original large-distance point with the finite remaining
carriers and its full original join quotient. No carrier-exclusion callback
or MS93 earlier premise remains. -/
theorem binary_three_large_distance_point_finite_models
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
          IsSimpleGroup (K.map q) ∧ BinaryThreeFiniteSimpleCarrier (K.map q) := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel⟩ :=
    binary_three_large_distance_point_remaining_models
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
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
  have hjoin := binary_three_point_join_core_quotient d c.L b z hLS P hP
  have hremaining := binary_three_finite_simple_carrier
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) hB hKq hBKq.le hSB he hjoin hmodel
  exact ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hremaining⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
