module

public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.PGL2Cardinality
public import GorensteinWalter.PSL2CoreModelFacts

/-!
# Supplied-Sylow exclusion of the exceptional field-nine cover

A five-subgroup normalized by a full Sylow two-subgroup of PSL₂(9) would
have a proper normalizer containing that Sylow. Under the actual comparison
PSL₂(9)≃A₆, every such overgroup has order eight or twenty-four, neither
divisible by five. This excludes nine on the simple central quotient itself;
it does not identify a quasisimple cover with that central quotient.

The same marked five-subgroup excludes the field of order three by its
PSL₂ order. These are the numerical inputs needed before applying the
nonexceptional odd PSL₂ central-kernel theorem.

Source: Aschbacher--Smith A.3.15(1), printed pp.50--51, and the odd model
reduction in 6.1.4, printed pp.665--666. In A.3.15(1), the torus divisibility
also excludes nine because five does not divide 9−1.
-/

public section
open Subgroup GorensteinWalter Atlas.Comparisons.Exceptional
open scoped MatrixGroups
namespace Theory.PSL2

/-- The literal five-subgroup in PSL₂(9) cannot be normalized by the
supplied full Sylow two-subgroup. -/
theorem nine_no_quintic_sylow_normalization
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (X : Subgroup PSL(2,F)) (hX : Nat.card X = 5) (S : Sylow 2 PSL(2,F))
    (hSX : (S : Subgroup PSL(2,F)) ≤ normalizer (X : Set PSL(2,F))) : False := by
  let e := psl2Card9EquivAlt6 hF
  let Y := X.map e.toMonoidHom
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let D := normalizer (Y : Set (alternatingGroup (Fin 6)))
  have hY : Nat.card Y = 5 := by
    rw [card_map_of_injective e.injective]
    exact hX
  have hTD : (T : Subgroup (alternatingGroup (Fin 6))) ≤ D := by
    have hh := map_mono (f := e.toMonoidHom) hSX
    rwa [map_equiv_normalizer_eq] at hh
  have hD : D ≠ ⊤ := by
    intro he
    let : Y.Normal := normalizer_eq_top_iff.mp he
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    rcases (inferInstance : Y.Normal).eq_bot_or_eq_top with hb | ht
    · simp [hb] at hY
    · rw [ht, card_top, alt6_card] at hY
      omega
  have hfive : 5 ∣ Nat.card D := hY ▸ card_dvd_of_le Y.le_normalizer
  rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour T D hTD hD with h8 | h24
  · norm_num [h8] at hfive
  · norm_num [h24] at hfive

/-- The marked normalized five-subgroup forces both numerical hypotheses
of the ordinary odd PSL₂ central-kernel theorem. -/
theorem odd_quintic_field_bounds
    {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (X : Subgroup PSL(2,F)) (hX : Nat.card X = 5) (S : Sylow 2 PSL(2,F))
    (hSX : (S : Subgroup PSL(2,F)) ≤ normalizer (X : Set PSL(2,F))) :
    3 < Nat.card F ∧ Nat.card F ≠ 9 := by
  constructor
  · have hthree := odd_prime_power_three_le _ hF
    by_contra hn
    have he : Nat.card F = 3 := by omega
    have hd := X.card_subgroup_dvd_card
    rw [hX, psl2_card_formula F hF, he] at hd
    norm_num at hd
  · intro hn
    exact nine_no_quintic_sylow_normalization hn X hX S hSX

end Theory.PSL2
