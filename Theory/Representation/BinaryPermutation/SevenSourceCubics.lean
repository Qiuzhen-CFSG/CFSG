module
public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner

/-!
# The two source cubics at a seven-letter four-set

The disjoint cycles on {0,1,6} and {2,3,4} fix the even word supported on
{2,3,4,5}. Each generates an index-three overgroup with the standard Sylow
two-subgroup, with quotient S₃ by its two-core. Together the cycles give an
actual elementary group of order nine. These are the two source actors
used to lift the weight-four point stabilizer in 14.7.50.

The small certificates involve only nine elements and seven coordinates;
the Sylow-overgroup quotients are proved from their indices.
Source: Aschbacher–Smith 14.7.50, printed p.1065, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Equiv Representation
open scoped BigOperators
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace BinaryPermutation.SevenSourceCubics
abbrev S7 := Perm (Fin 7)
def first : S7 := swap 0 1 * swap 1 6
def second : S7 := swap 2 3 * swap 3 4
def firstGroup : Subgroup S7 := zpowers first
def secondGroup : Subgroup S7 := zpowers second

theorem first_order : orderOf first = 3 :=
  orderOf_eq_prime (by decide : first ^ 3 = 1) (by decide)
theorem second_order : orderOf second = 3 :=
  orderOf_eq_prime (by decide : second ^ 3 = 1) (by decide)

theorem first_card : Nat.card firstGroup = 3 := (Nat.card_zpowers first).trans first_order
theorem second_card : Nat.card secondGroup = 3 := (Nat.card_zpowers second).trans second_order

private theorem cubic_join_quotient (r : S7) (hr : orderOf r = 3)
    (P : Subgroup S7) (hSP : standardTwo ≤ P) (hrP : r ∈ P)
    (hP : Nat.card P = 48) (t : S7) (ht : t ∈ standardTwo)
    (hnt : r * t * r⁻¹ ∉ standardTwo) :
    Nonempty (((zpowers r ⊔ standardTwo : Subgroup S7) ⧸
      pCore 2 (zpowers r ⊔ standardTwo : Subgroup S7)) ≃* Perm (Fin 3)) := by
  let J := zpowers r ⊔ standardTwo
  have hJP : J ≤ P := sup_le (zpowers_le.mpr hrP) hSP
  have hSJ : standardTwo ≤ J := le_sup_right
  have h3 : 3 ∣ Nat.card J := by
    have hh := card_dvd_of_le (show zpowers r ≤ J from le_sup_left)
    rwa [Nat.card_zpowers,hr] at hh
  have h16 : 16 ∣ Nat.card J := standardTwo_card ▸ card_dvd_of_le hSJ
  have hd : 48 ∣ Nat.card J :=
    (show Nat.Coprime 3 16 by decide).mul_dvd_of_dvd_of_dvd h3 h16
  have hj : Nat.card J = 48 := le_antisymm
    (hP ▸ card_le_of_le hJP) (Nat.le_of_dvd Nat.card_pos hd)
  let S := standardSylow.subtype hSJ
  have hs : Nat.card S = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv).trans standardTwo_card
  have hi : (S : Subgroup J).index = 3 := by
    have hh := (S : Subgroup J).card_mul_index
    rw [hs,hj] at hh
    omega
  apply sylow_index_three_core_quotient S hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
  intro he
  have hn : (S : Subgroup J).Normal := he ▸ inferInstance
  have hnorm : J ≤ normalizer (standardTwo : Set S7) :=
    (normal_subgroupOf_iff_le_normalizer hSJ).mp hn
  exact hnt ((mem_normalizer_iff.mp (hnorm ((show zpowers r ≤ J from le_sup_left) (mem_zpowers r))) t).mp ht)

/-- The cubic on the three-block satisfies exactly the source S₃ hypothesis. -/
theorem first_join_quotient :
    Nonempty (((firstGroup ⊔ standardTwo : Subgroup S7) ⧸
      pCore 2 (firstGroup ⊔ standardTwo : Subgroup S7)) ≃* Perm (Fin 3)) := by
  apply cubic_join_quotient first first_order cubicOvergroup _ (by decide)
    cubicOvergroup_card (swap 0 1) (by decide) (by decide)
  intro g hg
  obtain ⟨i,hi⟩ := sylowEquiv.surjective ⟨g,hg⟩
  have he : sylowWord i = g := congrArg Subtype.val hi
  rw [←he]
  exact (show ∀ i : Fin 16, sylowWord i ∈ cubicOvergroup by decide +kernel) i

/-- The cubic on the four-block also has the literal source S₃ Sylow join. -/
theorem second_join_quotient :
    Nonempty (((secondGroup ⊔ standardTwo : Subgroup S7) ⧸
      pCore 2 (secondGroup ⊔ standardTwo : Subgroup S7)) ≃* Perm (Fin 3)) :=
  cubic_join_quotient second second_order duadOvergroup inf_le_left (by decide)
    duadOvergroup_card (swap 2 3) (by decide) (by decide)

private abbrev Nine := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
private def embedding : Nine →* S7 where
  toFun a := first ^ a.1.toAdd.val * second ^ a.2.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- The two specified cubic axes contribute three-rank two. -/
theorem two_le_join_rank : 2 ≤ primeRank 3 (firstGroup ⊔ secondGroup : Subgroup S7) := by
  let f : Nine →* (firstGroup ⊔ secondGroup : Subgroup S7) := embedding.codRestrict _ (by
    intro a
    exact mul_mem ((show firstGroup ≤ firstGroup ⊔ secondGroup from le_sup_left)
      (pow_mem (mem_zpowers first) _))
      ((show secondGroup ≤ firstGroup ⊔ secondGroup from le_sup_right)
      (pow_mem (mem_zpowers second) _)))
  apply primeRank_ge_of_elementary_embedding (p := 3)
    (show ∀ a : Nine, a ^ 3 = 1 by decide)
    (show Nat.card Nine = 3 ^ 2 by simp [Nine]) f
  intro a b hab
  exact (show Function.Injective embedding by decide +kernel) (congrArg Subtype.val hab)

/-- The source weight-four point, in the standard Sylow coordinates. -/
def point : core (Fin 7) := ⟨![0,0,1,1,1,1,0], by
  change (∑ i : Fin 7, (![0,0,1,1,1,1,0] : Fin 7 → ZMod 2) i) = 0
  decide⟩

private theorem first_fixes : coreRepresentation (Fin 7) first point = point := by
  apply Subtype.ext
  decide
private theorem second_fixes : coreRepresentation (Fin 7) second point = point := by
  apply Subtype.ext
  decide

theorem firstGroup_fixes : ∀ a ∈ firstGroup, coreRepresentation (Fin 7) a point = point := by
  exact (show firstGroup ≤ BinaryNaturalDual.VectorStabilizers.representationStabilizer (coreRepresentation (Fin 7)) point from
    zpowers_le.mpr first_fixes)
theorem secondGroup_fixes : ∀ a ∈ secondGroup, coreRepresentation (Fin 7) a point = point := by
  exact (show secondGroup ≤ BinaryNaturalDual.VectorStabilizers.representationStabilizer (coreRepresentation (Fin 7)) point from
    zpowers_le.mpr second_fixes)
end BinaryPermutation.SevenSourceCubics
