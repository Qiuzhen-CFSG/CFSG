module

public import Theory.Representation.AlternatingSevenConjugatePair
public import Theory.Representation.AlternatingSevenConjugatePair.Model
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair.Parameters
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair.FixedFamily

/-!
# H.8: parameters for A₇ on `4 ⊕ 4̄`

A genuine pair here consists of two complementary inequivalent irreducible
binary four-spaces for A₇, with an actual faithful S₇ action interchanging
those spaces. `source_H_8` proves `m₂ = 3`, `m = 4`, `a = 2`, `β ≥ 4`,
and `α = ∞`, together with the singleton Sylow fixed-space family, its
fixed-plane characterization, and the order-three fixed-plane witness.
`source_H_8_group_geometry` supplies the two actual rank-three subgroup
classes and identifies the standing solvable residual with A₇.

The offender proof uses an odd element of a hypothetical rank-three actor.
Its inner intersection fixes a nonzero vector in the first summand, and
minimal displacement makes that vector fixed by the whole actor. Interchange
of the summands then gives a contradiction. The fixed-space family of
parameter three would supply such an offender, proving the upper bound on `a`.

All local calculation premises are discharged by the imported model and
subgroup theorems. `concrete_parameters` applies the result to `Model.pair`,
whose summands are identified by actual intertwining equivalences with the
natural four-space restricted through A₇ → A₈ ≃ SL₄(2) and its outer conjugate.
The earlier conditional interfaces remain available for the local argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.8, printed p.389/PDF p.400, with the standing hypotheses on printed p.377.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.AlternatingPair

open Representation.BinaryOffender Representation.AlternatingSevenConjugatePair

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The pair is an eight-dimensional module, from the actual direct-sum decomposition. -/
theorem pair_dimension (D : Pair V) : Module.finrank (ZMod 2) V = 8 := by
  have h := Submodule.finrank_add_eq_of_isCompl D.complementary
  rw [D.first_dim, D.second_dim] at h
  exact h.symm

/-- The final H.8 argument, conditional only on the group-rank and involution
 calculations. It excludes rank-three actors using their odd elements. -/
theorem no_offender_of_local_calculations (D : Pair V)
    (hrank : ∀ A : Subgroup (Equiv.Perm (Fin 7)), IsElementaryTwo A → rank A ≤ 3)
    (hinner : ∀ A : Subgroup (Equiv.Perm (Fin 7)), IsElementaryTwo A →
      A ≤ alternatingGroup (Fin 7) → rank A ≤ 2)
    (hinv : ∀ t : Equiv.Perm (Fin 7), orderOf t = 2 →
      4 ≤ fixedCodim D.representation (Subgroup.zpowers t))
    (A : Subgroup (Equiv.Perm (Fin 7))) : ¬ IsFMinusOneOffender D.representation A := by
  rintro ⟨hA, hcodim⟩
  have hU : D.first.toSubmodule ≠ ⊥ := by
    intro he
    have h := D.first_dim
    rw [he] at h
    simp at h
  have hlt := rank_add_one_lt_fixedCodim_of_swapped_summands D.representation
    (alternatingGroup (Fin 7)) alternatingGroup.index_eq_two
    D.first.toSubmodule D.second.toSubmodule hU D.complementary.disjoint
    (fun g hg u hu => D.first.apply_mem_toSubmodule ⟨g, hg⟩ hu)
    D.swap_first hrank hinner hinv hA
  omega

/-- The upper bound on `a` follows from the same exclusion: a rank-three
 member of `A₃` has the same fixed space as any of its involutions. -/
theorem moduleA_le_two_of_local_calculations (D : Pair V)
    (hrank : ∀ A : Subgroup (Equiv.Perm (Fin 7)), IsElementaryTwo A → rank A ≤ 3)
    (hinner : ∀ A : Subgroup (Equiv.Perm (Fin 7)), IsElementaryTwo A →
      A ≤ alternatingGroup (Fin 7) → rank A ≤ 2)
    (hinv : ∀ t : Equiv.Perm (Fin 7), orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) :
    ChapterE.moduleA D.representation ≤ 2 := by
  apply iSup_le
  intro k
  apply iSup_le
  rintro ⟨A, hA⟩
  apply ENat.natCast_le_natCast.mpr
  change k ≤ 2
  by_contra hk
  have hk3 : 3 ≤ k := by omega
  have hrle := ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily D.representation D.faithful hA
  have hr3 : rank A = 3 := by have := hrank A hA.2.1; omega
  let _ : IsElementaryAbelian 2 A := hA.2.1.2
  obtain ⟨t, htA, ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.2.1.1
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htA) ht
  have hCA : Subgroup.zpowers t ≤ A := Subgroup.zpowers_le.mpr htA
  have hp := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 7)))
    (Subgroup.zpowers t) A bot_le hCA
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    Nat.card_zpowers, ht2, hA.2.1.card_eq_two_pow_rank, hr3] at hp
  have hi : (Subgroup.zpowers t).relIndex A = 4 := by omega
  have heq := hA.2.2 (Subgroup.zpowers t) hCA (by
    rw [hi, show Nat.log 2 4 = 2 by decide]
    omega)
  have hc : fixedCodim D.representation A = 4 := by
    unfold fixedCodim
    rw [heq]
    exact hinv t ht2
  exact no_offender_of_local_calculations D hrank hinner (fun t ht => (hinv t ht).ge)
    A ⟨hA.2.1, by rw [hc, hr3]⟩

/-- Conditional numerical assembly. Concrete model calculations must supply
 the displayed premises before this is a proof of H.8. -/
theorem parameters_of_local_calculations (D : Pair V)
    (hrank : ∀ A : Subgroup (Equiv.Perm (Fin 7)), IsElementaryTwo A → rank A ≤ 3)
    (hinner : ∀ A : Subgroup (Equiv.Perm (Fin 7)), IsElementaryTwo A →
      A ≤ alternatingGroup (Fin 7) → rank A ≤ 2)
    (hinv : ∀ t : Equiv.Perm (Fin 7), orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4)
    (hodd : ∀ x : Equiv.Perm (Fin 7), (orderOf x).Prime → orderOf x ≠ 2 →
      4 ≤ fixedCodim D.representation (Subgroup.zpowers x)) :
    ChapterE.moduleM D.representation = 4 ∧
    ChapterE.moduleA D.representation ≤ 2 ∧
    4 ≤ moduleBeta D.representation ∧
    (∀ A, ¬ IsFMinusOneOffender D.representation A) ∧
    moduleAlpha D.representation = ⊤ := by
  have hno := no_offender_of_local_calculations D hrank hinner (fun t ht => (hinv t ht).ge)
  refine ⟨moduleM_eq_of_constant_involution_codim D.representation ?_ hinv,
    moduleA_le_two_of_local_calculations D hrank hinner hinv,
    le_moduleBeta_of_odd_prime_codim D.representation hodd, hno,
    moduleAlpha_eq_top_of_no_offender D.representation hno⟩
  exact ⟨Equiv.swap (0 : Fin 7) 1, orderOf_eq_prime (by decide) (by decide)⟩

open Representation.AlternatingSevenConjugatePair.ElementaryGeometry

/-- H.8's group calculation: the two genuine order-eight elementary subgroups
attain the two-rank and exhaust its rank-three conjugacy classes. The residual
identity identifies the source's `L := M∞` with the literal alternating group. -/
theorem source_H_8_group_geometry :
    Subgroup.solvableResidual S7 = alternatingGroup (Fin 7) ∧
    primeRank 2 S7 = 3 ∧ primeRank 2 (alternatingGroup (Fin 7)) = 2 ∧
    IsElementaryTwo pairElementary ∧ Nat.card pairElementary = 8 ∧
    rank pairElementary = 3 ∧
    IsElementaryTwo fourTwoElementary ∧ Nat.card fourTwoElementary = 8 ∧
    rank fourTwoElementary = 3 ∧
    (∀ g : S7, pairElementary.map (MulAut.conj g).toMonoidHom ≠ fourTwoElementary) ∧
    (∀ A : Subgroup S7, IsElementaryTwo A → rank A = 3 →
      ∃ g : S7, A.map (MulAut.conj g).toMonoidHom = pairElementary ∨
        A.map (MulAut.conj g).toMonoidHom = fourTwoElementary) :=
  ⟨solvableResidual_symmetric, primeRank_symmetric, primeRank_alternating,
    pairElementary_isElementaryTwo, pairElementary_card, pairElementary_rank,
    fourTwoElementary_isElementaryTwo, fourTwoElementary_card, fourTwoElementary_rank,
    representatives_not_conjugate, elementary_rank_three_conjugacy⟩

/-- The numerical parameters and offender exclusion in H.8 for every genuine
conjugate pair, with all group and element calculations discharged. -/
theorem parameters (D : Pair V) :
    primeRank 2 S7 = 3 ∧
    ChapterE.moduleM D.representation = 4 ∧
    ChapterE.moduleA D.representation = 2 ∧
    4 ≤ moduleBeta D.representation ∧
    (∀ A, ¬ IsFMinusOneOffender D.representation A) ∧
    moduleAlpha D.representation = ⊤ := by
  obtain ⟨hm, ha, hb, hno, halpha⟩ := parameters_of_local_calculations D
    rank_le_three rank_le_two_of_le_alternating D.involution_fixedCodim
    D.odd_prime_fixedCodim
  exact ⟨primeRank_symmetric, hm,
    le_antisymm ha (two_le_moduleA D D.involution_fixedCodim), hb, hno, halpha⟩

/-- H.8, printed p.389: all parameters, their element witnesses, and the
precise singleton family in an arbitrary Sylow two-subgroup. In particular,
the unique member is an actual four-group of A₇, characterized by its two
fixed planes. No local calculation or offender-exclusion premise remains. -/
theorem source_H_8 (D : Pair V) (T : Sylow 2 S7) :
    primeRank 2 S7 = 3 ∧
    ChapterE.moduleM D.representation = 4 ∧
    (∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) ∧
    ChapterE.moduleA D.representation = 2 ∧
    (∃ A : Subgroup S7, A ≤ (T : Subgroup S7) ∧ A ≤ alternatingGroup (Fin 7) ∧
      IsElementaryTwo A ∧ rank A = 2 ∧
      sylowFixedSpaceFamily D.representation T 2 = {A} ∧
      Module.finrank (ZMod 2) (D.firstFixedSpace A) = 2 ∧
      Module.finrank (ZMod 2) (D.secondFixedSpace A) = 2 ∧
      (∀ B : Subgroup S7, B ≤ (T : Subgroup S7) → B ≤ alternatingGroup (Fin 7) →
        IsElementaryTwo B → rank B = 2 →
        (B = A ↔ Module.finrank (ZMod 2) (D.firstFixedSpace B) = 2 ∧
          Module.finrank (ZMod 2) (D.secondFixedSpace B) = 2))) ∧
    4 ≤ moduleBeta D.representation ∧
    (∃ x : S7, x ∈ alternatingGroup (Fin 7) ∧ orderOf x = 3 ∧
      Module.finrank (ZMod 2) (D.firstFixedSpace (Subgroup.zpowers x)) = 2 ∧
      Module.finrank (ZMod 2) (D.secondFixedSpace (Subgroup.zpowers x)) = 2) ∧
    (∀ A, ¬ IsFMinusOneOffender D.representation A) ∧
    moduleAlpha D.representation = ⊤ := by
  obtain ⟨hr, hm, ha, hb, hno, halpha⟩ := parameters D
  exact ⟨hr, hm, D.involution_fixedCodim, ha,
    exists_sylowFixedSpaceFamily_singleton D D.involution_fixedCodim T,
    hb, D.exists_order_three_fixed_planes, hno, halpha⟩

/-- The parameter theorem is inhabited by the concrete natural/outer-natural
model on `Four × Four`, constructed through the actual exceptional isomorphism. -/
theorem concrete_parameters :
    primeRank 2 S7 = 3 ∧
    ChapterE.moduleM Model.pair.representation = 4 ∧
    ChapterE.moduleA Model.pair.representation = 2 ∧
    4 ≤ moduleBeta Model.pair.representation ∧
    (∀ A, ¬ IsFMinusOneOffender Model.pair.representation A) ∧
    moduleAlpha Model.pair.representation = ⊤ :=
  parameters Model.pair

end CFSG.Quasithin.ChapterH.AlternatingPair
