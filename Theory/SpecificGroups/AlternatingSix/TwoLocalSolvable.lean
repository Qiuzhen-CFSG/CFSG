module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.Alternating.SmallFixedComponents
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.GroupTheory.SmallIndexSolvable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupTheory.SolvableResidual

/-!
# Two-local solvability in Aut(A₆)

Every nontrivial two-subgroup of Aut(A₆) has solvable normalizer. A perfect
subgroup normalizing such a subgroup centralizes its elementary central layer:
the induced automorphism image has order dividing both 168 and 1440, hence 24.
The perfect subgroup then lifts to A₆ and lies in the solvable fixed group of
an involutory automorphism. Applying this to the solvable residual proves the
normalizer assertion.

This supplies the A₆ and 3.A₆ exclusions in the constrained rank-one block
argument, Aschbacher–Smith C.4.1 and 4.3.7, pp.151–153 and 615–616. The proof
uses the actual automorphism group, including its exceptional outer automorphisms.
-/

public section

open Subgroup Theory.GroupTheory
namespace AlternatingSix.ShadowLocal

private theorem solvable_of_card_dvd_twenty_four {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G ∣ 24) : Group.IsSolvable G := by
  let P : Sylow 2 G := Classical.choice inferInstance
  have hcop : Nat.Coprime (P : Subgroup G).index (2 ^ 3) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index).symm.pow_right 3
  have hi : (P : Subgroup G).index ∣ 3 :=
    hcop.dvd_of_dvd_mul_left ((P : Subgroup G).index_dvd_card.trans hc)
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact (P : Subgroup G).isSolvable_of_index_le_four
    ((Nat.le_of_dvd (by decide : 0 < 3) hi).trans (by decide))

private theorem perfect_centralizes_elementary
    (B E : Subgroup AutA6) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (hn : B ≤ normalizer (E : Set AutA6)) : B ≤ centralizer (E : Set AutA6) := by
  let f := E.normalizerMonoidHom.comp (inclusion hn)
  obtain ⟨j,hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := 3) E (elementary_card_le_eight E)
  have h168 : Nat.card f.range ∣ 168 := by
    have hd := card_dvd_of_injective (j.comp f.range.subtype)
      (hj.comp f.range.subtype_injective)
    have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    rwa [hc] at hd
  have h1440 : Nat.card f.range ∣ 1440 :=
    (card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective).trans
      (card_aut ▸ B.card_subgroup_dvd_card)
  have h24 : Nat.card f.range ∣ 24 := by
    simpa using Nat.dvd_gcd h168 h1440
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsSolvable f.range := solvable_of_card_dvd_twenty_four h24
  have hs : Subsingleton f.range := by
    by_contra! hh
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro b hb e he
  have hh : f ⟨b,hb⟩ = 1 := congrArg Subtype.val
    (hs.elim (f.rangeRestrict ⟨b,hb⟩) 1)
  have hv := congrArg (fun a : MulAut E => (a ⟨e,he⟩ : AutA6)) hh
  change b * e * b⁻¹ = e at hv
  exact (mul_inv_eq_iff_eq_mul.mp hv).symm

/-- No nontrivial perfect subgroup of Aut(A6) normalizes a nontrivial two-subgroup. -/
theorem no_perfect_two_normalizer
    (B R : Subgroup AutA6) [Group.IsPerfect B]
    (hB : B ≠ ⊥) (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    (hn : B ≤ normalizer (R : Set AutA6)) : False := by
  let E := omegaCenterIn R
  have hE : E ≠ ⊥ := by
    intro he
    have hh := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup R R le_rfl hp R.le_normalizer hR
    change R ⊓ E ≠ ⊥ at hh
    rw [he,inf_bot_eq] at hh
    exact hh rfl
  have hBE : B ≤ centralizer (E : Set AutA6) := perfect_centralizes_elementary B E
    (hn.trans (normalizer_le_normalizer_omegaCenterIn R))
  obtain ⟨a,ha,ha1⟩ := E.bot_or_exists_ne_one.resolve_left hE
  have ha2 : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  let : Group.IsSolvable (MulAut.Outer A6) := outer_isSolvable
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift B
    (alternatingGroup.center_eq_bot (by simp))
  have hfix (b : B) : f b ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply inner_injective
    have hc := hBE b.property a ha
    have he : MulAut.conj (a (f b)) = a * MulAut.conj (f b) * a⁻¹ := by
      ext x
      simp
    rw [he,hconj,hc,mul_inv_cancel_right]
  let f' : B →* a.fixedSubgroup := f.codRestrict _ hfix
  let : Group.IsSolvable a.fixedSubgroup :=
    alternatingGroup.SmallFixedComponents.six_fixed_solvable a ha2
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := f') (fun x y h => hf (congrArg Subtype.val h))
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
  exact Group.IsPerfect.not_isSolvable B inferInstance

/-- Every nontrivial two-subgroup of Aut(A6) has solvable normalizer. -/
theorem two_normalizer_solvable
    (R : Subgroup AutA6) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    Group.IsSolvable (normalizer (R : Set AutA6)) := by
  let N := normalizer (R : Set AutA6)
  let B := (solvableResidual N).map N.subtype
  let : Group.IsPerfect B := Group.IsPerfect.map N.subtype
  have hB : B = ⊥ := by
    by_contra hh
    exact no_perfect_two_normalizer B R hh hR hp (map_subtype_le _)
  have hres : solvableResidual N = ⊥ :=
    ((solvableResidual N).map_eq_bot_iff_of_injective N.subtype_injective).mp hB
  obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := N)
  exact ⟨n,hn.trans hres⟩

end AlternatingSix.ShadowLocal
