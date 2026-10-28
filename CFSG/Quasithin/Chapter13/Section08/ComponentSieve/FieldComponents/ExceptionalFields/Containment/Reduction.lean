module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.ModelOrders
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.LocalThreePart
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.NormalizerRank
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.SourceInput

/-!
# Exceptional noncontainment: the source reduction

The genuine B_C identities put O^{3′}(B) in L₁. Its nontrivial three-part,
relative normality and the two-perfect local seed force the covered A₆
case and |B|₃ = 3. The actual earlier quotient equivalences retain the
nonsplit cover and E₉. Nine-divisibility in the special linear and special
unitary Borels then leaves the actual PSL₂(4) and PSU₃(8) alternatives.

This module also exports the constructed Borel Sylow marking and the
proved rank-one input to the exact earlier 13.7.5(5) implication.

`exceptional_noncontainment` discharges `BorelOrderFacts` using the actual
exceptional model calculations. It restricts the exact earlier theta
identity on H ∩ M to BL₁ and retains the source local setup, both B_C
identities, the index-three identity, and the prescribed outer actor.
The intermediate Borel dichotomy, failure of external X, the separate
projective L₃(4) exclusion, and the earlier chapter conclusions are
explicit inputs. The parent still owns the two surviving contradictions
and final containment L₁ ≤ K; neither is asserted here.
Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
open HigherFieldReduction Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The actual cover and model reduction, with the intrinsic Borel
arithmetic explicit for reuse. The three-generated subgroup is
constructed, proved nontrivial and placed in L₁; none of those conclusions
is an input field. -/
theorem exceptional_noncontainment_of_borel_orders
    (H K L L₁ L₀ X L₁plus : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (models : ExceptionalModels (Source.starImage H K))
    (earlier : EarlierSeedModels L L₁ X L₁plus)
    (orders : BorelOrderFacts H K hKH S)
    (hL₀ : L₀ ≤ L₁) (hp : IsPPerfect 2 L₁)
    (htheta : L₁ = closure {x : G |
      x ∈ borelResidual (componentBorel H K hKH S) ⊔ L₁ ∧ orderOf x = 3})
    (hprod : borelResidual (componentBorel H K hKH S) ⊔ L₁ =
      centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L ⊔ L₁)
    (hBC : centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L =
        residualIn 3 (borelResidual (componentBorel H K hKH S)) ∨
      centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L =
        residualIn 3 (borelResidual (componentBorel H K hKH S)) ⊔ L₀)
    (hL₁B : L₁ ≤ normalizer (borelResidual (componentBorel H K hKH S) : Set G))
    (hout : ¬ L₁ ≤ K) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    Nonempty ((L₁ ⧸ pCore 2 L₁) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧ X = L₁plus ∧
    3 ^ (Nat.card (borelResidual (componentBorel H K hKH S))).factorization 3 = 3 ∧
    (primeToResidual 3 (borelResidual (componentBorel H K hKH S))).map
      (borelResidual (componentBorel H K hKH S)).subtype ≠ ⊥ ∧
    (primeToResidual 3 (borelResidual (componentBorel H K hKH S))).map
      (borelResidual (componentBorel H K hKH S)).subtype ≤ L₁ ∧
    (ClassicalGroup.IsPSL (Source.starImage H K) 2 4 ∨
      ClassicalGroup.IsPSU (Source.starImage H K) 3 8) := by
  let B := borelResidual (componentBorel H K hKH S)
  have hBK : B ≤ K := (map_subtype_le _).trans (borelLift_le H K hKH _)
  have hY := threeGenerated_le_seed B L₁ L L₀ hL₀ htheta hprod hBC
    orders.threeResidual_coprime
  have hlo := (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp
    orders.three_dvd
  change 1 ≤ (Nat.card B).factorization 3 at hlo
  rcases earlier with ⟨_, hq, _⟩ | ⟨eL, ⟨e₉⟩, hX⟩
  · have hlt := borel_three_valuation_lt_of_outside B K L₁ hBK hout hY hL₁B hp 1
      (by simpa only [pow_one] using hq)
    omega
  · have hq : Nat.card (L₁ ⧸ pCore 2 L₁) = 9 := by
      rw [Nat.card_congr e₉.toEquiv]
      simp
    have hpart := (noncontainment_three_part B K L₁ hBK hout hY hL₁B hp
      orders.three_dvd (Or.inr hq)).2
    have hval : (Nat.card B).factorization 3 = 1 := by
      apply Nat.pow_right_injective (by decide : 1 < 3)
      simpa only [pow_one] using hpart
    have hnine : ¬ 9 ∣ Nat.card B := by
      intro hd
      have htwo : 2 ≤ (Nat.card B).factorization 3 :=
        (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hd
      omega
    refine ⟨eL, ⟨e₉⟩, hX, hpart, threeGenerated_ne_bot B orders.three_dvd, hY, ?_⟩
    rcases models with h | h | h | h
    · exact Or.inl h
    · exact (hnine (orders.specialLinear_nine h)).elim
    · exact Or.inr h
    · exact (hnine (orders.specialUnitary_nine h)).elim

/-- The exceptional noncontainment reduction from the source local setup
and earlier conclusions. The Borel order calculations and local theta
restriction are proved, and the same source element t* retains its outer
action. The two remaining actual models are passed to the independent
unitary and central-factor exclusions owned by the containment assembly. -/
theorem exceptional_noncontainment
    (H K L L₁ L₀ X L₁plus G₁ M V : Subgroup G) (T : Sylow 2 G)
    (hKH : K ≤ H) (S : Sylow 2 K) (t : H)
    (s : SourceBorelInput H K L L₁ L₀ X L₁plus G₁ M V T hKH S t)
    (hcases : BorelAlternative.{_,0} H K X (QuotientGroup.mk t))
    (hnoexternal : ¬ ExternalXAlternative H K X)
    (hnotprojective : ¬ ClassicalGroup.IsPSL (Source.starImage H K) 3 4)
    (hout : ¬ L₁ ≤ K) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    Nonempty ((L₁ ⧸ pCore 2 L₁) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧ X = L₁plus ∧
    3 ^ (Nat.card (borelResidual (componentBorel H K hKH S))).factorization 3 = 3 ∧
    (primeToResidual 3 (borelResidual (componentBorel H K hKH S))).map
      (borelResidual (componentBorel H K hKH S)).subtype ≠ ⊥ ∧
    (primeToResidual 3 (borelResidual (componentBorel H K hKH S))).map
      (borelResidual (componentBorel H K hKH S)).subtype ≤ L₁ ∧
    (ClassicalGroup.IsPSL (Source.starImage H K) 2 4 ∨
      ClassicalGroup.IsPSU (Source.starImage H K) 3 8) ∧
    OuterStarAction H K (QuotientGroup.mk t) := by
  obtain ⟨hmodel, houter⟩ := hcases.resolve_left hnoexternal
  have models := exceptionalModels_of_carrier hmodel hnotprojective
  have hBC : centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L =
        residualIn 3 (borelResidual (componentBorel H K hKH S)) ∨
      centralizingResidual (borelResidual (componentBorel H K hKH S)) L₁ L =
        residualIn 3 (borelResidual (componentBorel H K hKH S)) ⊔ L₀ := by
    rcases s.earlier with ⟨hL, _, _⟩ | ⟨hL, _, _⟩
    · exact Or.inl (s.ordinary_centralizer hL)
    · exact Or.inr (s.covered_centralizer hL)
  obtain ⟨hcover, hnine, hX, hpart, hne, hle, hmodels⟩ :=
    exceptional_noncontainment_of_borel_orders H K L L₁ L₀ X L₁plus hKH S models s.earlier
      (borelOrderFacts_of_exceptionalModels H K hKH S models) s.zero_le s.seed_twoPerfect
      s.theta_borel s.product hBC s.seed_normalizes_borel hout
  exact ⟨hcover, hnine, hX, hpart, hne, hle, hmodels, houter⟩

/-- In the contained PSL₂(4) branch, the earlier local models supply the
nontrivial three-part. The proved normalizer-rank calculation then applies
the exact universal 13.7.5(5) input to give the ordinary A₆ quotient.
The normalizer is that of the literal section V₃/V₁, not a presumed
point stabilizer in a permutation action. -/
theorem ordinary_six_of_contained_source
    (H K L L₁ L₀ X L₁plus G₁ M V V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf H).Normal]
    (hKH : K ≤ H) (S : Sylow 2 K) (t : H)
    (s : SourceBorelInput H K L L₁ L₀ X L₁plus G₁ M V T hKH S t)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 4)
    (hL₁K : L₁ ≤ K) (hV₃H : V₃ ≤ H) (hV₁ : V₁ ≤ V₃)
    (hL₁N : L₁ ≤ normalizer (V₃ : Set G))
    (h1375 : ∀ J : Subgroup G, J ≤ H → (J.subgroupOf H).IsCComponent →
      X ≤ J → L₁ ≤ J → primeRank 3 (seedSectionNormalizer H J V₃ V₁) = 1 →
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  have hlocal : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ∨
      Nat.card (L₁ ⧸ pCore 2 L₁) = 9 := by
    rcases s.earlier with ⟨_, hc, _⟩ | ⟨_, ⟨e₉⟩, _⟩
    · exact Or.inl hc
    · right
      rw [Nat.card_congr e₉.toEquiv]
      simp
  exact ordinary_six_of_contained_linear_two_four hF H K L L₁ X V₃ V₁
    hKH hV₃H hV₁ e s.component (s.chosen_seed_le.trans hL₁K) hL₁K hL₁N hlocal h1375

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
