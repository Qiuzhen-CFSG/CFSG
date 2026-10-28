module
public import Theory.GroupAction.MarkedCubicRecognition.CentralSeed
public import Theory.GroupTheory.CubicResidualJoin
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The actual central-cubic parabolic in the Heisenberg alternative

The intrinsic center of the three-core is inverted by an element of every
Sylow two-subgroup. Its literal preimage two-residual therefore has full
Sylow commutator and gives an S₃ quotient after adjoining that Sylow.
The same quotient map gives |S| = 4 |O₂(X)|. These facts construct the
second vertex and force the nonzero core in the original second amalgam
of Chapter13 Section04; no cubic lift or action marking is supplied.

Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup
namespace MarkedCubicRecognition
local instance : Finite HeisenbergExtension := Finite.of_equiv (HeisenbergPrime 3 × Four)
  (SemidirectProduct.equivProd (N := HeisenbergPrime 3) (G := Four)
    (φ := heisenbergAction)).symm
variable {X : Type*} [Group X] [Finite X]

/-- The literal central residual has full Sylow movement and S₃ parabolic quotient. -/
theorem centralThreeResidual_parabolic
    (S : Sylow 2 X) (e : (X ⧸ pCore 2 X) ≃* HeisenbergExtension) :
    ⁅centralThreeResidual X,(S : Subgroup X)⁆ = centralThreeResidual X ∧
      Nonempty (((centralThreeResidual X ⊔ (S : Subgroup X) : Subgroup X) ⧸
        pCore 2 (centralThreeResidual X ⊔ (S : Subgroup X) : Subgroup X)) ≃*
          Equiv.Perm (Fin 3)) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let R := centralThreeResidual X
  let : R.Normal := centralThreeResidual_normal
  have hm : R.map q = (center (pCore 3 HeisenbergExtension)).map
      (pCore 3 HeisenbergExtension).subtype := by
    dsimp only [q,R]
    rw [←map_map,centralThreeResidual_image e,map_embeddedCenter _ _ e.injective,pCore_map_iso]
  have hc : Nat.card (R.map q) = 3 := by rw [hm,heisenberg_threeCore_center_card]
  have hmove : ¬ (S : Subgroup X).map q ≤ centralizer (R.map q : Set HeisenbergExtension) := by
    intro hcent
    obtain ⟨c,s,hgen,hc,hs,hinv⟩ := center_generator_inverted (S.mapSurjective hq)
    have hcR : c ∈ R.map q := by rw [hm,←hgen]; exact mem_zpowers c
    have he : c*s = s*c := hcent hs c hcR
    have he' : c = c^2 := mul_right_cancel (he.trans hinv)
    have hc1 : c = 1 := by
      have h := he'
      rw [pow_two] at h
      exact (mul_eq_left.mp h.symm)
    rw [hc1,orderOf_one] at hc
    omega
  have hp : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 (centralThreePreimage X)
  obtain ⟨hcomm,_,he⟩ := cubic_join_of_moving_prime_image R S q hp S.isPGroup'
    le_normalizer_of_normal hc
    ((hk ▸ pCore_isPGroup).to_le inf_le_right)
    (inf_le_right.trans (hk ▸ pCore_isPGroup.le_sylow_of_normal S)) hmove
  exact ⟨hcomm,he⟩

/-- The original Sylow has order four times the full two-core. -/
theorem sylow_card_eq_four_mul_twoCore
    (S : Sylow 2 X) (e : (X ⧸ pCore 2 X) ≃* HeisenbergExtension) :
    Nat.card S = 4 * Nat.card (pCore 2 X) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hks : q.ker ≤ (S : Subgroup X) := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  have hcard : Nat.card HeisenbergExtension = 108 := by
    rw [Nat.card_congr (SemidirectProduct.equivProd (N := HeisenbergPrime 3)
      (G := Four) (φ := heisenbergAction)),Nat.card_prod,HeisenbergPrime.card]
    norm_num [Four,C2,Nat.card_prod,Nat.card_zmod]
  have hS : Nat.card ((S : Subgroup X).map q) = 4 := by
    change Nat.card (S.mapSurjective hq) = 4
    rw [Sylow.card_eq_multiplicity,hcard]
    decide +kernel
  have hh := (q.ker.subgroupOf (S : Subgroup X)).index_mul_card
  change q.ker.relIndex (S : Subgroup X) * Nat.card (q.ker.subgroupOf (S : Subgroup X)) = _ at hh
  rw [relIndex_ker,Nat.card_congr (subgroupOfEquivOfLe hks).toEquiv,hS,hk] at hh
  exact hh.symm
end MarkedCubicRecognition
