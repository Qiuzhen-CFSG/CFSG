module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Source
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.GroupTheory.SolvableRadical

/-!
# Solvability of the original plus quotient modulo its component

The original actor is K L_v T_v, since T_v normalizes K. Modulo K⁺ it is
a homomorphic image of L_v T_v. The full L_v is solvable because its two-core
quotient has order three; T_v is a two-group normalizing L_v. Thus the quotient
by K⁺ is solvable without discarding either original action kernel.

Source: Aschbacher–Smith13.6.15, printed p.930, using13.6.14 and the local
cubic residual from the earlier13.6 setup.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
open ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem solvable_join_of_normalizes (H S : Subgroup G)
    [Group.IsSolvable H] [Group.IsSolvable S] (hn : S ≤ normalizer (H : Set G)) :
    Group.IsSolvable (H ⊔ S : Subgroup G) := by
  let P := H ⊔ S
  let : (H.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le H.le_normalizer hn)
  let : Group.IsSolvable (H.subgroupOf P) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show H ≤ P from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show H ≤ P from le_sup_left)).injective
  let : Group.IsSolvable (S.subgroupOf P) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show S ≤ P from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show S ≤ P from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top (H.subgroupOf P) (S.subgroupOf P)
  apply map_injective P.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show H ≤ P from le_sup_left),
    map_subgroupOf_eq_of_le (show S ≤ P from le_sup_right)]
  simp only [← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- The literal plus quotient modulo K⁺ is solvable: it is an image of
L_v T_v, retaining its full two-core. -/
theorem plus_quotient_isSolvable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3) :
    let := plusImage_K_normal K L T z v hL hz hK hn
    Group.IsSolvable (Gplus K L T z v hL hz ⧸ plusImage K L T z v hL hz K) := by
  let := plusImage_K_normal K L T z v hL hz hK hn
  dsimp only
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Group.IsNilpotent (pCore 2 (Lv L v)) := pCore_isPGroup.isNilpotent
  let : IsCyclic (Lv L v ⧸ pCore 2 (Lv L v)) := isCyclic_of_prime_card hc
  let : Group.IsSolvable (Lv L v) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 (Lv L v))).mpr
      ⟨inferInstance, inferInstance⟩
  let : Group.IsNilpotent (Tv T v) := (Chapter1.isSylowIn_iff.mp hSylow).1.isNilpotent
  let H := Lv L v ⊔ Tv T v
  let : Group.IsSolvable H := solvable_join_of_normalizes _ _ hL
  let A := plusActor K L T v
  have hHA : H ≤ A := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hKA : K ≤ A := K_le_plusActor K L T v
  let f := plusMk K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let q := QuotientGroup.mk' C
  let p := q.comp f
  have hgen : K ⊔ H = A := by
    dsimp [H, A, plusActor]
    rw [Kminus_eq_of_invariant K T v hn, sup_assoc]
  have hs : Function.Surjective (p.comp (inclusion hHA)) := by
    apply MonoidHom.range_eq_top.mp
    have hall : (⊤ : Subgroup A).map p = ⊤ :=
      map_top_of_surjective _ ((QuotientGroup.mk'_surjective C).comp
        (plusMk_surjective K L T z v hL hz))
    have hj : K.subgroupOf A ⊔ H.subgroupOf A = ⊤ := by
      apply map_injective A.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKA, map_subgroupOf_eq_of_le hHA, hgen]
      simp only [← MonoidHom.range_eq_map, range_subtype]
    have hkill : (K.subgroupOf A).map p = ⊥ := by
      apply bot_unique
      rintro _ ⟨a, ha, rfl⟩
      exact (QuotientGroup.eq_one_iff (N := C) (f a)).mpr (mem_map_of_mem f ha)
    have hh : (H.subgroupOf A).map p = ⊤ := by
      rw [← hj, Subgroup.map_sup, hkill, bot_sup_eq] at hall
      exact hall
    rw [← hh, MonoidHom.range_comp]
    congr 1
    ext a
    constructor
    · rintro ⟨h, rfl⟩
      exact h.property
    · intro ha
      exact ⟨⟨a.val, ha⟩, rfl⟩
  exact Group.isSolvable_of_surjective hs

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
