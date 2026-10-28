module

public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Stabilizers
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Transfer

/-!
# Small subgroup indices in A₆

A proper subgroup of index at most 63 has index divisible by five, or index
6 or 36. Simplicity excludes indices below six. The remaining exceptions
would have orders 15, 20, 30, 40, or 45. A normal subgroup of order five
has a unique fixed letter, putting its overgroup inside the corresponding
A₅. Simplicity of that A₅ rules out four orders; Burnside transfer reduces
order 30 to order 15.

This elementary bound is used to count nonzero vector orbits in binary
simple A₆ modules of dimension at most six. It supplies a sufficient route
to the point-stabilizer step of Aschbacher–Smith K.1.2, printed p.452,
without a subgroup or representation catalogue.
-/

@[expose] public section
namespace AlternatingSix.SmallIndex
open Subgroup
local notation "A6" => alternatingGroup (Fin 6)

private theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- Restriction to the complement, with an actual labelling of its letters. -/
noncomputable def pointEquiv {n : ℕ} (i : Fin (n + 1)) :
    MulAction.stabilizer (alternatingGroup (Fin (n + 1))) i ≃*
      alternatingGroup (Fin n) := by
  classical
  have he : MulAction.stabilizer (alternatingGroup (Fin (n + 1))) i =
      fixingSubgroup (alternatingGroup (Fin (n + 1)))
        (({i} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
    ext g
    simp [MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff]
  have hc : Fintype.card (↑(({i} : Finset (Fin (n + 1)))ᶜ)) = n := by simp
  exact (MulEquiv.subgroupCongr he).trans
    ((Atlas.Families.Alternating.stabilizerComplementEquiv {i}).trans
      (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq hc)))

private theorem point_card (i : Fin 6) :
    Nat.card (MulAction.stabilizer A6 i) = 60 := by
  rw [Nat.card_congr (pointEquiv (n := 5) i).toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem normal_five_fixes (H : Subgroup A6) (P : Subgroup H)
    [P.Normal] (hc : Nat.card P = 5) :
    ∃ i : Fin 6, H ≤ MulAction.stabilizer A6 i := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hm := hp.card_modEq_card_fixedPoints (Fin 6)
  have hb : Nat.card (MulAction.fixedPoints P (Fin 6)) ≤ 6 :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans_eq (Nat.card_fin 6)
  have hn : Nat.card (MulAction.fixedPoints P (Fin 6)) ≠ 6 := by
    intro he
    have hs : Function.Surjective (Subtype.val : MulAction.fixedPoints P (Fin 6) → Fin 6) :=
      ((Nat.bijective_iff_injective_and_card _).mpr
        ⟨Subtype.val_injective, he.trans (Nat.card_fin 6).symm⟩).surjective
    have htriv : Subsingleton P := by
      apply subsingleton_of_forall_eq 1
      intro x
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Equiv.ext
      intro i
      obtain ⟨j, rfl⟩ := hs i
      exact j.property x
    have hone : Nat.card P = 1 := by
      let := htriv
      exact Nat.card_eq_one_iff_unique.mpr ⟨htriv, inferInstance⟩
    omega
  rw [Nat.card_fin] at hm
  change 6 % 5 = Nat.card (MulAction.fixedPoints P (Fin 6)) % 5 at hm
  have hcard : Nat.card (MulAction.fixedPoints P (Fin 6)) = 1 := by omega
  obtain ⟨hsub, hnon⟩ := Nat.card_eq_one_iff_unique.mp hcard
  let i := hnon.some
  refine ⟨i.val, ?_⟩
  intro g hg
  exact congrArg Subtype.val (hsub.elim
    (⟨(⟨g, hg⟩ : H) • i.val, smul_mem_fixedPoints_of_normal (⟨g, hg⟩ : H) i.property⟩ :
      MulAction.fixedPoints P (Fin 6)) i)

private theorem not_exceptional_order (H : Subgroup A6)
    (hc : Nat.card H = 15 ∨ Nat.card H = 20 ∨ Nat.card H = 40 ∨ Nat.card H = 45) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 H := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity]
    rcases hc with hc | hc | hc | hc <;> rw [hc] <;> decide +kernel
  have hi : (P : Subgroup H).index = 3 ∨ (P : Subgroup H).index = 4 ∨
      (P : Subgroup H).index = 8 ∨ (P : Subgroup H).index = 9 := by
    have h := (P : Subgroup H).card_mul_index
    rw [hP] at h
    rcases hc with hc | hc | hc | hc <;> omega
  have hn : Nat.card (Sylow 5 H) = 1 := by
    have hd := P.card_dvd_index
    have hm := card_sylow_modEq_one 5 H
    change Nat.card (Sylow 5 H) % 5 = 1 % 5 at hm
    have hb : Nat.card (Sylow 5 H) ≤ 9 :=
      (Nat.le_of_dvd (by omega : 0 < (P : Subgroup H).index) hd).trans (by omega)
    interval_cases hn : Nat.card (Sylow 5 H) <;> rcases hi with hi | hi | hi | hi <;> omega
  let : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hn).1
  let : (P : Subgroup H).Normal := P.normal_of_subsingleton
  obtain ⟨i, hle⟩ := normal_five_fixes H P hP
  let K := MulAction.stabilizer A6 i
  let J := H.subgroupOf K
  let : IsSimpleGroup K := (pointEquiv (n := 5) i).isSimpleGroup
  have hJ : Nat.card J = Nat.card H := Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have hK : Nat.card K = 60 := point_card i
  have ht : J ≠ ⊤ := by
    intro he
    rw [he, card_top, hK] at hJ
    rcases hc with hc | hc | hc | hc <;> omega
  have hb : 5 ≤ J.index := by
    by_contra h
    apply ht
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hf := Nat.factorial_le (show J.index ≤ 4 by omega)
    rw [hK]
    norm_num [Nat.factorial] at hf ⊢
    omega
  have hprod := J.card_mul_index
  rw [hJ, hK] at hprod
  have hlarge : 15 ≤ Nat.card H := by rcases hc with hc | hc | hc | hc <;> omega
  nlinarith

private theorem not_thirty (H : Subgroup A6) (hc : Nat.card H = 30) : False := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P : Sylow 2 H := Classical.choice inferInstance
  have hP : Nat.card P = 2 := by
    rw [Sylow.card_eq_multiplicity, hc]
    decide +kernel
  have hcyc : IsCyclic P := isCyclic_of_prime_card hP
  have hmin : (Nat.card H).minFac = 2 := by rw [hc]; decide
  let N := (MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hmin)).ker
  have hn : Nat.card N = 15 := by
    have hp := (hcyc.isComplement' hmin).card_mul_card
    change Nat.card N * Nat.card P = Nat.card H at hp
    rw [hc, hP] at hp
    omega
  apply not_exceptional_order (N.map H.subtype)
  left
  rwa [card_map_of_injective H.subtype_injective]

/-- The only proper indices at most 63 not divisible by five are 6 and 36. -/
theorem index_divisible_by_five_or_six_or_thirtySix (H : Subgroup A6)
    (hproper : H ≠ ⊤) (hbound : H.index ≤ 63) :
    5 ∣ H.index ∨ H.index = 6 ∨ H.index = 36 := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have hlo : 6 ≤ H.index := by
    by_contra h
    apply hproper
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hf := Nat.factorial_le (show H.index ≤ 5 by omega)
    rw [card_A6]
    norm_num [Nat.factorial] at hf ⊢
    omega
  by_contra! hn
  have hp := H.card_mul_index
  rw [card_A6] at hp
  have hc : Nat.card H = 15 ∨ Nat.card H = 20 ∨ Nat.card H = 30 ∨
      Nat.card H = 40 ∨ Nat.card H = 45 := by
    interval_cases hi : H.index <;> omega
  rcases hc with hc | hc | hc | hc | hc
  · exact not_exceptional_order H (Or.inl hc)
  · exact not_exceptional_order H (Or.inr (Or.inl hc))
  · exact not_thirty H hc
  · exact not_exceptional_order H (Or.inr (Or.inr (Or.inl hc)))
  · exact not_exceptional_order H (Or.inr (Or.inr (Or.inr hc)))
end AlternatingSix.SmallIndex
