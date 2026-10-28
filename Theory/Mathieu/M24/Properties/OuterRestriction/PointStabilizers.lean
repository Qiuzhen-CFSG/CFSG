module

public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension
public import Theory.GroupAction.FixedPointOfSmallIndex
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeDegree
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Data.Nat.Squarefree

/-!
# Abstract automorphisms preserve the natural M24 point stabilizers

Every proper subgroup of the concrete M23 of index at most 24 has index 23.
Simplicity and the prime divisor 23 exclude smaller indices. An index-24
subgroup would meet the heptad stabilizer, of coprime index 253, in index 24.
The latter stabilizer has kernel of order 16 and quotient A7, so its putative
subgroup projects to order 105, 210, 420, or 840 in A7. Small-index simplicity
excludes the last two. The first two are squarefree orders: their cyclic
Sylow subgroups make the commutator cyclic, and a faithful transitive action
of prime degree seven then bounds the whole group order by 7 * 6.

Orbit counting now shows that every M23 action on 24 points has a fixed
point, since all nontrivial orbits would have size 23. Restricting the natural
M24 action along an abstract automorphism and the actual M23 point-stabilizer
equivalence therefore gives containment in a point stabilizer. Equality follows
from their common index 24. No reconstruction or automorphism premise remains.

Source: Aschbacher, *Sporadic Groups*, Chapter 7, Exercise 5, printed p.107;
GLS3, Table 5.3e. The concrete heptad extension is the M23 specialization of
Aschbacher, Lemma 19.1, already proved in `HeptadStructure.SplitExtension`.
-/

namespace Sporadic.Mathieu.M24OuterRestriction

open Subgroup MulAction Atlas.GroupTheory M23Geometry
open scoped IsMulCommutative

/-- An abelian faithful transitive action is regular. -/
private theorem abelian_card_of_transitive
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [IsMulCommutative G] [IsPretransitive G X] (x : X) :
    Nat.card G = Nat.card X := by
  apply Nat.card_congr
  apply Equiv.ofBijective (fun g : G => g • x)
  refine ⟨?_, fun y => exists_smul_eq G x y⟩
  intro a b hab
  apply eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨g, rfl⟩ := exists_smul_eq G x y
  change a • x = b • x at hab
  rw [← mul_smul, mul_comm a g, mul_smul, hab, ← mul_smul, mul_comm g b, mul_smul]

/-- In prime degree a nontrivial cyclic derived group is regular and normal. -/
private theorem zgroup_card_le_of_prime_degree
    (G : Type*) [Group G] [Finite G] [IsZGroup G] {p : ℕ} [hp : Fact p.Prime]
    [MulAction G (Fin p)] [FaithfulSMul G (Fin p)] [IsPretransitive G (Fin p)] :
    Nat.card G ≤ p * (p - 1) := by
  let x : Fin p := ⟨0, hp.out.pos⟩
  let : IsPreprimitive G (Fin p) := IsPreprimitive.of_prime_card (by simpa using hp.out)
  by_cases hc : commutator G = ⊥
  · let : IsMulCommutative G := (commutator_eq_bot_iff G).mp hc
    rw [abelian_card_of_transitive G (Fin p) x, Nat.card_fin]
    have := hp.out.two_le
    calc
      p = p * 1 := (mul_one p).symm
      _ ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
  · let : IsCyclic (commutator G) := IsZGroup.isCyclic_commutator G
    let : IsPretransitive (commutator G) (Fin p) := normal_pretransitive _ hc
    have hcard : Nat.card (commutator G) = p := by
      simpa only [Nat.card_fin] using abelian_card_of_transitive (commutator G) (Fin p) x
    have hbound := prime_normalizer_card_bound (G := G) (commutator G) x p hcard
      (Nat.card_fin p)
    rw [Subgroup.normalizer_eq_top, Nat.card_congr (Subgroup.topEquiv.toEquiv)] at hbound
    exact hbound

private theorem alternatingSeven_card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem alternatingSeven_no_card (H : Subgroup (alternatingGroup (Fin 7)))
    (hc : Nat.card H = 105 ∨ Nat.card H = 210) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsZGroup H := IsZGroup.of_squarefree (by rcases hc with hc | hc <;> rw [hc] <;> decide +kernel)
  let P : Sylow 7 H := Classical.choice inferInstance
  have h7 : 7 ∣ Nat.card H := by rcases hc with hc | hc <;> rw [hc] <;> norm_num
  have h49 : ¬ 7 ^ 2 ∣ Nat.card H := by rcases hc with hc | hc <;> rw [hc] <;> norm_num
  have hP : Nat.card P = 7 := sylow_card_prime 7 h7 h49 P
  let : IsPretransitive P (Fin 7) := prime_subgroup_pretransitive (G := H) 7
    (Nat.card_fin 7) P hP
  let : IsPretransitive H (Fin 7) := ⟨fun x y => by
    obtain ⟨g, hg⟩ := exists_smul_eq P x y
    exact ⟨g.val, hg⟩⟩
  have hb := zgroup_card_le_of_prime_degree H (p := 7)
  rcases hc with hc | hc <;> omega

private theorem alternatingSeven_no_large_divisor (H : Subgroup (alternatingGroup (Fin 7)))
    (hc : Nat.card H = 105 ∨ Nat.card H = 210 ∨ Nat.card H = 420 ∨ Nat.card H = 840) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hc with hc | hc | hc | hc
  · exact alternatingSeven_no_card H (Or.inl hc)
  · exact alternatingSeven_no_card H (Or.inr hc)
  all_goals
    have hmul := H.card_mul_index
    rw [alternatingSeven_card, hc] at hmul
    have hi : H.index = 6 ∨ H.index = 3 := by omega
    have hs : H.index.factorial < Nat.card (alternatingGroup (Fin 7)) := by
      rw [alternatingSeven_card]
      rcases hi with hi | hi <;> rw [hi] <;> decide +kernel
    have htop := subgroup_eq_top_of_index_factorial_lt H hs
    rw [htop, Nat.card_congr (Subgroup.topEquiv.toEquiv), alternatingSeven_card] at hc
    omega

/-- The kernel order and alternating quotient exclude index 24 locally. -/
private theorem heptad_no_index_twentyFour (I : Subgroup heptadStabilizer) : I.index ≠ 24 := by
  intro hi
  have hI : Nat.card I = 1680 := by
    have h := I.card_mul_index
    rw [hi, heptadStabilizer_card] at h
    omega
  let φ : I →* alternatingGroup (Fin 7) := heptadAlternatingAction.comp I.subtype
  have hk : Nat.card φ.ker ∣ 16 := by
    have h := Subgroup.card_comap_dvd_of_injective heptadAlternatingAction.ker
      I.subtype I.subtype_injective
    rw [MonoidHom.comap_ker] at h
    rw [heptadAlternatingAction_ker, heptadKernel_card] at h
    exact h
  have hmul : Nat.card φ.ker * Nat.card φ.range = 1680 := by
    have h := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hI] at h
    exact h
  have hd : Nat.card φ.range ∣ 2520 := alternatingSeven_card ▸ φ.range.card_subgroup_dvd_card
  have hr : Nat.card φ.range = 105 ∨ Nat.card φ.range = 210 ∨
      Nat.card φ.range = 420 ∨ Nat.card φ.range = 840 := by
    have hk' : Nat.card φ.ker = 1 ∨ Nat.card φ.ker = 2 ∨ Nat.card φ.ker = 4 ∨
        Nat.card φ.ker = 8 ∨ Nat.card φ.ker = 16 := by
      have ha : ∀ k ∈ Nat.divisors 16, k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 := by decide +kernel
      exact ha _ (Nat.mem_divisors.mpr ⟨hk, by decide⟩)
    rcases hk' with hk' | hk' | hk' | hk' | hk' <;> rw [hk'] at hmul
    · have hh : Nat.card φ.range = 1680 := by omega
      rw [hh] at hd
      norm_num at hd
    all_goals omega
  exact alternatingSeven_no_large_divisor φ.range hr

/-- Coprimality with the heptad index transfers a putative index 24. -/
private theorem m23_no_index_twentyFour (K : Subgroup M23) : K.index ≠ 24 := by
  intro hK
  have hd : 24 ∣ (heptadStabilizer ⊓ K).index :=
    hK ▸ Subgroup.index_dvd_of_le (show heptadStabilizer ⊓ K ≤ K from inf_le_right)
  rw [← Subgroup.relIndex_mul_index (show heptadStabilizer ⊓ K ≤ heptadStabilizer from inf_le_left),
    Subgroup.inf_relIndex_left, heptadStabilizer_index] at hd
  have hdiv : 24 ∣ K.relIndex heptadStabilizer :=
    (show Nat.Coprime 24 253 by decide).dvd_of_dvd_mul_right hd
  have hbound : K.relIndex heptadStabilizer ≤ 24 := by
    have h := Subgroup.relIndex_le_of_le_right (H := K) (K := heptadStabilizer)
      (L := ⊤) le_top (by simp [Subgroup.relIndex_top_right, hK])
    simpa only [Subgroup.relIndex_top_right, hK] using h
  have hpos : 0 < K.relIndex heptadStabilizer :=
    Nat.pos_of_ne_zero (K.subgroupOf heptadStabilizer).index_ne_zero_of_finite
  exact heptad_no_index_twentyFour (K.subgroupOf heptadStabilizer)
    (le_antisymm hbound (Nat.le_of_dvd hpos hdiv))

/-- The only proper subgroup index at most 24 is 23. -/
private theorem m23_small_index (K : Subgroup M23) (hK : K ≠ ⊤) (hb : K.index ≤ 24) :
    K.index = 23 := by
  classical
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  let f := MulAction.toPermHom M23 (M23 ⧸ K)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply hK
      apply top_le_iff.mp
      rw [← h, ← Subgroup.normalCore_eq_ker]
      exact K.normalCore_le
  have hd : 23 ∣ K.index.factorial := by
    have hdiv := Subgroup.card_dvd_of_injective f hf
    have he : Nat.card (Equiv.Perm (M23 ⧸ K)) = K.index.factorial := by
      let := Fintype.ofFinite (M23 ⧸ K)
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    rw [he, m23_order] at hdiv
    exact (by norm_num : 23 ∣ 10200960).trans hdiv
  have hl : 23 ≤ K.index := (Nat.Prime.dvd_factorial (by decide : Nat.Prime 23)).mp hd
  have hn := m23_no_index_twentyFour K
  omega

/-- This holds for any action, including restrictions twisted by automorphisms. -/
private theorem m23_fixed_point [MulAction M23 (Fin 24)] :
    ∃ x : Fin 24, ∀ g : M23, g • x = x := by
  apply exists_fixedPoint_of_smallIndex_dvd (d := 23)
  · intro K hK hb
    rw [m23_small_index K hK (by simpa only [Nat.card_fin] using hb)]
  · norm_num

/-- Every abstract automorphism preserves the class of natural point stabilizers. -/
public theorem point_stabilizers_map (f : MulAut M24) :
    ∃ x : Fin 24, (stabilizer M24 (24 : Fin 24)).map f.toMonoidHom = stabilizer M24 x := by
  let H := stabilizer M24 (24 : Fin 24)
  let φ : M23 →* M24 := f.toMonoidHom.comp
    (H.subtype.comp m23EquivM24PointStabilizer.toMonoidHom)
  let : MulAction M23 (Fin 24) := MulAction.compHom (Fin 24) φ
  obtain ⟨x, hx⟩ := m23_fixed_point
  have hle : H.map f.toMonoidHom ≤ stabilizer M24 x := by
    rintro g ⟨h, hh, rfl⟩
    obtain ⟨k, hk⟩ := m23EquivM24PointStabilizer.surjective ⟨h, hh⟩
    have hfix := hx k
    change f (m23EquivM24PointStabilizer k : M24) • x = x at hfix
    change f h • x = x
    simpa only [hk] using hfix
  refine ⟨x, le_antisymm hle ?_⟩
  apply Subgroup.relIndex_eq_one.mp
  have hi (y : Fin 24) : (stabilizer M24 y).index = 24 := by
    simpa only [Nat.card_fin] using index_stabilizer_of_transitive M24 y
  have hm := Subgroup.relIndex_mul_index hle
  rw [Subgroup.index_map_of_bijective f.bijective, hi, hi] at hm
  change (H.map f.toMonoidHom).relIndex (stabilizer M24 x) = 1
  omega

end Sporadic.Mathieu.M24OuterRestriction
