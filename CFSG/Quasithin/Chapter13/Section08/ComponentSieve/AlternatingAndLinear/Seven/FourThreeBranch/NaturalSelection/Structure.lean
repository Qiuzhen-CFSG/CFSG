module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Stabilizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Factors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Surjectivity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.LocalRank
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CoveredAlternative

/-!
# Conditional structural reductions for the four-plus-three branch

This file supplies conditional reductions for the structural part of 13.8.24. The
stabilizer is the inverse image through the actual map `H → H/O₂(H)`, and the
universal solvable-overgroup lemma gives one containment in `H ∩ M`.  The
other containment is obtained from the actual star image of `H ∩ M`; no
maximality certificate is used in place of that source containment.

The rank calculation keeps the two inputs separate: an elementary abelian
subgroup of order nine gives the lower bound, while the actual four-plus-three
image and its two-core kernel give the upper bound.  The ordinary A₆ and
covered-A₆ quotient alternatives are then fed to the earlier covered-quotient
calculation, producing a genuine equivalence with the concrete hexacode
carrier.  Finally, two weak inclusions and cardinal equalities identify the
marked residual factors, and the literal fixing/inverting actor gives
surjectivity onto `S₇`.

The containment/cardinality assumptions on the two marked images are
equivalent to their desired equalities. Likewise the concrete cycle action
has not been derived here from the source action modulo O₂(L₁). Accordingly
`fourThree_structure` is a conditional helper, not the structural source
theorem. `Structure.Theta` removes the stabilizer-containment and elementary-nine
premises; `Structure.ThetaImage` identifies the actual cubic-generated image.
The remaining residual marking and quotient-action deductions stay with the
NaturalSelection assembly.

Source: Aschbacher--Smith, 13.7.3(9), 13.7.5, 13.8.13 and 13.8.24,
printed pp.938, 950--951 and 958--959 (1 March 2004 manuscript).
-/

@[expose] public section

open Equiv Subgroup
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.LocalRank

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

variable {G : Type*} [Group G] [Finite G]

/-! ## The relative stabilizer -/

/- The source containment used here is weaker than the equality being proved:
it only says that the star image of `H ∩ M` lies in the partition stabilizer. -/
theorem relativeStabilizer_eq_inter
    (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ)
    (hinter : Source.starImage H (H ⊓ M) ≤ fourThreeStabilizer.comap φ) :
    relativeStabilizer H φ = H ⊓ M := by
  apply le_antisymm
  · exact relativeStabilizer_le_inter H L₁ T G₁ M hbase hHG h13 φ hφ hP
  · intro x hx
    let a : H := ⟨x, hx.1⟩
    let q : H →* Source.Hstar H := QuotientGroup.mk' (pCore 2 H)
    have hq : q a ∈ Source.starImage H (H ⊓ M) := by
      change q a ∈ ((H ⊓ M).subgroupOf H).map q
      exact ⟨⟨x, hx.1⟩, hx, rfl⟩
    have hstab : φ (q a) ∈ fourThreeStabilizer := hinter hq
    change x ∈ ((fourThreeStabilizer.comap φ).comap q).map H.subtype
    exact ⟨a, hstab, rfl⟩

/-! ## Rank two -/

/- The order calculation is intrinsic to the literal `S₄ × S₃` stabilizer;
it is not an extra hypothesis about the local group. -/
theorem fourThreeStabilizer_threeRank_le_two :
    primeRank 3 fourThreeStabilizer ≤ 2 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply (primeRank_le_iff_elementary_card_le fourThreeStabilizer).mpr
  intro E hE
  obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
  have hdiv : 3 ^ n ∣ 144 := by
    rw [← fourThreeStabilizer_card]
    exact hn ▸ E.card_subgroup_dvd_card
  have hn2 : n ≤ 2 := by
    by_contra! hn2
    have hbad : 3 ^ 3 ∣ 144 :=
      (pow_dvd_pow 3 (show 3 ≤ n by omega)).trans hdiv
    norm_num at hbad
  rw [hn]
  exact pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) hn2

theorem primeRank_three_eq_two_of_fourThree
    (H L₁ T : Subgroup G) (hL₁H : L₁ ≤ H)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ)
    (E : Subgroup L₁) (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 9) : primeRank 3 L₁ = 2 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsElementaryAbelian 3 E := hE
  let q : L₁ →* Source.Hstar H :=
    (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hL₁H)
  have hmem (x : L₁) : φ (q x) ∈ fourThreeStabilizer := by
    have hx : q x ∈ Source.starImage H L₁ := by
      exact ⟨⟨x, hL₁H x.property⟩, x.property, rfl⟩
    exact hP (starImage_mono H le_sup_left hx)
  let f : L₁ →* fourThreeStabilizer :=
    (φ.comp q).codRestrict fourThreeStabilizer hmem
  have hker : f.ker = q.ker := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.codRestrict_apply,
      MonoidHom.comp_apply, Subtype.ext_iff]
    change φ (q x) = (1 : S7) ↔ q x = 1
    rw [← φ.map_one, hφ.eq_iff]
  have hqker : IsPGroup 2 q.ker := by
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 H)).ker.comap (inclusion hL₁H))
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hL₁H)
  have hk0 : primeRank 3 f.ker = 0 := by
    rw [hker]
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := hqker.exists_card_dvd_pow
    intro hd
    exact (by decide : ¬ 3 ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow (hd.trans hn))
  have hu : primeRank 3 L₁ ≤ 2 := by
    calc
      primeRank 3 L₁ ≤ primeRank 3 f.ker + primeRank 3 fourThreeStabilizer :=
        Theory.GroupTheory.primeRank_le_ker_add f
      _ = primeRank 3 fourThreeStabilizer := by rw [hk0, zero_add]
      _ ≤ 2 := fourThreeStabilizer_threeRank_le_two
  have hl : 2 ≤ primeRank 3 L₁ := by
    simpa only [show (3 : ℕ) ^ 2 = 9 by norm_num] using
      (IsElementaryAbelian.primeRank_ge_of_card E hEcard)
  omega

/-! ## The covered quotient -/

noncomputable def quotient_equiv_hexEven_of_threeRank_two
    (L L₁ : Subgroup G)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hrank : primeRank 3 L₁ = 2) :
    (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms :=
  Classical.choice (Components.Swapped.LinearTwo.covered_quotient_of_threeRank_two
    L L₁ hmodels ha6 hrank)

/-! ## Marked residual factors -/

theorem markedFactors_of_source_containments
    {J : Type*} [Group J] (φ : J →* S7) (L₀ X : Subgroup J)
    (hmark :
      ((L₀.map φ ≤ threeFactor ∧ X.map φ ≤ fourResidualFactor ∧
          Nat.card threeFactor ≤ Nat.card (L₀.map φ) ∧
          Nat.card fourResidualFactor ≤ Nat.card (X.map φ)) ∨
       (L₀.map φ ≤ fourResidualFactor ∧ X.map φ ≤ threeFactor ∧
          Nat.card fourResidualFactor ≤ Nat.card (L₀.map φ) ∧
          Nat.card threeFactor ≤ Nat.card (X.map φ)))) :
    MarkedFactors φ L₀ X := by
  rcases hmark with h | h
  · left
    exact ⟨Subgroup.eq_of_le_of_card_ge h.1 h.2.2.1,
      Subgroup.eq_of_le_of_card_ge h.2.1 h.2.2.2⟩
  · right
    exact ⟨Subgroup.eq_of_le_of_card_ge h.1 h.2.2.1,
      Subgroup.eq_of_le_of_card_ge h.2.1 h.2.2.2⟩

/-! ## Surjectivity -/

theorem surjective_of_source_inversion
    {J : Type*} [Group J] (φ : J →* S7) (K T : Subgroup J)
    (hK : K.map φ = alternatingGroup (Fin 7))
    (t : J) (ht : t ∈ T) (hT : T ≤ fourThreeStabilizer.comap φ)
    (hinv :
      (φ t * cycle012 * (φ t)⁻¹ = cycle012 ∧
        φ t * cycle456 * (φ t)⁻¹ = cycle456⁻¹) ∨
      (φ t * cycle456 * (φ t)⁻¹ = cycle456 ∧
        φ t * cycle012 * (φ t)⁻¹ = cycle012⁻¹)) :
    Function.Surjective φ := by
  have hAlt : alternatingGroup (Fin 7) ≤ φ.range := by
    rw [← hK]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, rfl⟩
  exact surjective_of_centralizes_and_inverts φ hAlt t (hT ht) hinv

/-! ## One assembly theorem -/

theorem fourThree_structure
    (H L₁ T G₁ M L K L₀ X : Subgroup G)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (S : Sylow 2 H) (_hS : (S : Subgroup H) = T.subgroupOf H)
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ)
    (hinter : Source.starImage H (H ⊓ M) ≤ fourThreeStabilizer.comap φ)
    (hL₁H : L₁ ≤ H)
    (E : Subgroup L₁) (hE : IsElementaryAbelian 3 E) (hEcard : Nat.card E = 9)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hmark :
      ((Source.starImage H L₀).map φ ≤ threeFactor ∧
          (Source.starImage H X).map φ ≤ fourResidualFactor ∧
          Nat.card threeFactor ≤ Nat.card ((Source.starImage H L₀).map φ) ∧
          Nat.card fourResidualFactor ≤ Nat.card ((Source.starImage H X).map φ)) ∨
       ((Source.starImage H L₀).map φ ≤ fourResidualFactor ∧
          (Source.starImage H X).map φ ≤ threeFactor ∧
          Nat.card fourResidualFactor ≤ Nat.card ((Source.starImage H L₀).map φ) ∧
          Nat.card threeFactor ≤ Nat.card ((Source.starImage H X).map φ)))
    (t : Source.Hstar H) (ht : t ∈ Source.starImage H T)
    (hinv :
      (φ t * cycle012 * (φ t)⁻¹ = cycle012 ∧
        φ t * cycle456 * (φ t)⁻¹ = cycle456⁻¹) ∨
      (φ t * cycle456 * (φ t)⁻¹ = cycle456 ∧
        φ t * cycle012 * (φ t)⁻¹ = cycle012⁻¹))
    (hK : (Source.starImage H K).map φ = alternatingGroup (Fin 7)) :
    relativeStabilizer H φ = H ⊓ M ∧
      primeRank 3 L₁ = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      MarkedFactors φ (Source.starImage H L₀) (Source.starImage H X) ∧
      Function.Surjective φ := by
  have hrank := primeRank_three_eq_two_of_fourThree H L₁ T hL₁H φ hφ hP E hE hEcard
  have hT : Source.starImage H T ≤ fourThreeStabilizer.comap φ :=
    (starImage_mono H le_sup_right).trans hP
  refine ⟨relativeStabilizer_eq_inter H L₁ T G₁ M hbase hHG h13 φ hφ hP hinter,
    hrank, ⟨quotient_equiv_hexEven_of_threeRank_two L L₁ hmodels ha6 hrank⟩,
    markedFactors_of_source_containments φ (Source.starImage H L₀)
      (Source.starImage H X) hmark, ?_⟩
  exact surjective_of_source_inversion φ (Source.starImage H K)
    (Source.starImage H T) hK t ht hT hinv

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

end
