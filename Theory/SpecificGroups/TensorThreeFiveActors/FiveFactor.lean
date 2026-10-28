module

public import Theory.SpecificGroups.TensorThreeFiveActors.Reduction
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Cubic actors in the actual five-point factors

In A₅, a subgroup with cubic quotient by its two-core is solvable. If a
Sylow four-group Q normalizes it, their join is a proper Sylow overgroup,
hence lies in N(Q). Divisibility by four and three makes the join equal
to this order-twelve normalizer. The actual point-stabilizer marking by A₄
makes the normalizer two-perfect, so its two-group quotient by the actor
is trivial.

In S₅, two-perfectness first places the actor inside A₅ = S₅∞. Restricting
the given Sylow subgroup to this normal A₅ and transporting the intrinsic
two-core quotient proves the same identification with the literal relative
normalizer. The product corollaries retain the independent splitting
contract as an explicit premise; the source assembly belongs to the parent.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.4.10(1), printed p.1010/PDF p.1027, under the two models in
14.4.2(5), printed p.1006/PDF p.1023.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.TensorThreeFiveActors.FiveFactor
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)

private theorem a4_twoPerfect : IsPPerfect 2 (alternatingGroup (Fin 4)) := by
  rw [← Equiv.Perm.twoResidual_eq_alternating]
  exact isPPerfect_pResidual 2

private theorem normalizer_marking (Q : Sylow 2 A5) :
    Nonempty (alternatingGroup (Fin 4) ≃* normalizer (Q : Set A5)) := by
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
  let : MulAction.IsPretransitive A5 (Fin 5) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 (4 : Fin 5) i
  rw [hi]
  exact ⟨BinaryPermutation.AlternatingFiveBorel.marking.trans
    (MulAction.stabilizerEquivStabilizer hg.symm)⟩

private theorem cubic_solvable {G : Type*} [Group G] [Finite G]
    (hc : Nat.card (G ⧸ pCore 2 G) = 3) : Group.IsSolvable G := by
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Group.IsNilpotent (G ⧸ pCore 2 G) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hc)).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 G)).mpr ⟨inferInstance, inferInstance⟩

/-- A cubic actor normalized by a Sylow four-group is its full normalizer. -/
theorem alternating_actor (Q : Sylow 2 A5) (B : Subgroup A5)
    (hn : (Q : Subgroup A5) ≤ normalizer (B : Set A5))
    (hc : Nat.card (B ⧸ pCore 2 B) = 3) :
    B = normalizer (Q : Set A5) := by
  let J : Subgroup A5 := (Q : Subgroup A5) ⊔ B
  let : Group.IsSolvable B := cubic_solvable hc
  let : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  have hsolv : Group.IsSolvable J := by
    let : Group.IsSolvable (B ⊔ (Q : Subgroup A5) : Subgroup A5) :=
      Group.isSolvable_sup_of_normalizes B Q hn
    let eJ : (B ⊔ (Q : Subgroup A5) : Subgroup A5) ≃* J :=
      MulEquiv.subgroupCongr (sup_comm _ _)
    exact Group.isSolvable_of_surjective (f := eJ.toMonoidHom) eJ.surjective
  let : Group.IsSolvable J := hsolv
  have hJN : J ≤ normalizer (Q : Set A5) :=
    alternatingGroup.solvable_sylow_overgroup_le_normalizer Q J le_sup_left
  obtain ⟨e⟩ := normalizer_marking Q
  have hNcard : Nat.card (normalizer (Q : Set A5)) = 12 := by
    rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have h3 : 3 ∣ Nat.card J := by
    have hd := (pCore 2 B).index_dvd_card
    rw [index_eq_card, hc] at hd
    exact hd.trans (card_dvd_of_le (show B ≤ J from le_sup_right))
  have h4 : 4 ∣ Nat.card J := by
    rw [← Theory.PSL2.SylowFixedQuotients.alternating_sylow_card Q]
    exact card_dvd_of_le (show (Q : Subgroup A5) ≤ J from le_sup_left)
  have h12 : 12 ∣ Nat.card J :=
    (show Nat.Coprime 4 3 by decide).mul_dvd_of_dvd_of_dvd h4 h3
  have hJ : J = normalizer (Q : Set A5) :=
    eq_of_le_of_card_ge hJN (by rw [hNcard]; exact Nat.le_of_dvd (Nat.card_pos) h12)
  have hpJ : IsPPerfect 2 J := by
    rw [hJ]
    exact a4_twoPerfect.of_surjective e.toMonoidHom e.surjective
  let : (B.subgroupOf (Q ⊔ B)).Normal := normal_subgroupOf_sup_of_le_normalizer hn
  let : (B.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer hn
  have hq : IsPGroup 2 (J ⧸ B.subgroupOf J) :=
    (Q.isPGroup'.to_quotient (B.subgroupOf Q)).of_equiv
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient Q B hn)
  have htop := hpJ (B.subgroupOf J) inferInstance hq
  have hBJ : B = J := by
    apply le_antisymm le_sup_right
    intro x hx
    exact show (⟨x, hx⟩ : J) ∈ B.subgroupOf J from htop ▸ mem_top _
  exact hBJ.trans hJ

private instance : Group.IsPerfect A5 :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

/-- The factor contract for the actual alternating group. -/
theorem alternating_factorActors : FactorActors A5 := by
  intro Q B hn _hp hc
  simpa only [solvableResidual_eq_top, inf_top_eq, top_inf_eq, Sylow.coe_coe] using alternating_actor Q B hn hc

private theorem symmetric_residual : solvableResidual S5 = A5 := by
  apply le_antisymm _ (le_solvableResidual_of_isPerfect A5)
  let : Group.IsNilpotent (S5 ⧸ A5) :=
    (IsPGroup.of_card (p := 2) (n := 1) (by
      rw [← index_eq_card, alternatingGroup.index_eq_two]
      rfl)).isNilpotent
  exact solvableResidual_le_of_solvable_quotient A5

/-- The factor contract in S₅ retains precisely the original Sylow intersection. -/
theorem symmetric_factorActors : FactorActors S5 := by
  intro Q B hn hp hc
  rw [symmetric_residual]
  have hBA : B ≤ A5 := by
    rw [← Equiv.Perm.twoResidual_eq_alternating]
    exact le_pResidual_of_isPPerfect B hp
  obtain ⟨P, hP⟩ := Q.exists_subgroupOf_eq_of_normal A5
  let B₀ := B.subgroupOf A5
  let e : B₀ ≃* B := subgroupOfEquivOfLe hBA
  have hc₀ : Nat.card (B₀ ⧸ pCore 2 B₀) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hc
  have hn₀ : (P : Subgroup A5) ≤ normalizer (B₀ : Set A5) := by
    rw [hP]
    exact (comap_mono (f := (A5).subtype) hn).trans (B.le_normalizer_comap (A5).subtype)
  have hB₀ := alternating_actor P B₀ hn₀ hc₀
  have hN : normalizer (P : Set A5) =
      (normalizer (((Q : Subgroup S5) ⊓ A5 : Subgroup S5) : Set S5)).subgroupOf A5 := by
    rw [subgroupOf_normalizer_eq inf_le_right]
    have hI : ((Q : Subgroup S5) ⊓ A5).subgroupOf A5 = (P : Subgroup A5) := by
      rw [hP]
      ext x
      exact ⟨And.left, fun hx => ⟨hx, x.property⟩⟩
    rw [hI, Sylow.coe_coe]
  rw [hN] at hB₀
  have hm := congrArg (map (A5).subtype) hB₀
  simpa only [B₀, map_subgroupOf_eq_of_le hBA, subgroupOf_map_subtype, inf_comm] using hm

/-- The S₃ × A₅ calculation, conditional only on the independent splitting contract. -/
theorem alternating_product_actors
    (hsplit : ProductSplitting A5)
    (Q : Sylow 2 (Equiv.Perm (Fin 3) × A5))
    (A : Subgroup (Equiv.Perm (Fin 3) × A5))
    (hn : (Q : Subgroup (Equiv.Perm (Fin 3) × A5)) ≤ normalizer (A : Set _))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 (Equiv.Perm (Fin 3) × A5) ∨
      A = solvableResidual (Equiv.Perm (Fin 3) × A5) ⊓ normalizer
        (((Q : Subgroup (Equiv.Perm (Fin 3) × A5)) ⊓
          solvableResidual (Equiv.Perm (Fin 3) × A5) : Subgroup _) : Set _) :=
  product_actors_of_factors TensorThreeFive.a5_threeCore_eq_bot
    hsplit alternating_factorActors Q A hn hp hc

/-- The S₃ × S₅ calculation, conditional only on the independent splitting contract. -/
theorem symmetric_product_actors
    (hsplit : ProductSplitting S5)
    (Q : Sylow 2 (Equiv.Perm (Fin 3) × S5))
    (A : Subgroup (Equiv.Perm (Fin 3) × S5))
    (hn : (Q : Subgroup (Equiv.Perm (Fin 3) × S5)) ≤ normalizer (A : Set _))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 (Equiv.Perm (Fin 3) × S5) ∨
      A = solvableResidual (Equiv.Perm (Fin 3) × S5) ⊓ normalizer
        (((Q : Subgroup (Equiv.Perm (Fin 3) × S5)) ⊓
          solvableResidual (Equiv.Perm (Fin 3) × S5) : Subgroup _) : Set _) :=
  product_actors_of_factors TensorThreeFive.s5_threeCore_eq_bot
    hsplit symmetric_factorActors Q A hn hp hc

end Theory.SpecificGroups.TensorThreeFiveActors.FiveFactor

end
