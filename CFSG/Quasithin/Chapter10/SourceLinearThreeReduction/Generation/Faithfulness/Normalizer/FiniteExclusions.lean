module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.QuotientGeometry
public import Theory.GroupTheory.PerfectPairOrder
public import Theory.Alternating.PrimeRank
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.SymplecticSix.OrderRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Finite component exclusions from the original two-factor quotient

The actual normalizer residual carries twice every odd rank of the original
perfect component quotient. Burnside's two-prime theorem rules out each
model whose order is squarefree away from two and a single odd prime.
The exact alternating ranks handle all degrees at most nine. The finite
rows use certified orders and actual group equivalences, including the
literal projective symplectic quotient and derived G₂ carrier.

Source: Aschbacher--Smith 4.4.12 and the following component inspection,
printed pp.622--623, as used in 10.2.3(2), p.745. Placement stays explicit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
private theorem squarefree_35 : Squarefree (35 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 5 7 by decide)).mpr
    ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree, (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩

private theorem squarefree_55 : Squarefree (55 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 5 11 by decide)).mpr
    ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree, (Nat.prime_iff.mp (by decide : Nat.Prime 11)).squarefree⟩

private theorem squarefree_385 : Squarefree (385 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 35 11 by decide)).mpr
    ⟨squarefree_35, (Nat.prime_iff.mp (by decide : Nat.Prime 11)).squarefree⟩

private theorem squarefree_1085 : Squarefree (1085 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 35 31 by decide)).mpr
    ⟨squarefree_35, (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩

private theorem squarefree_8855 : Squarefree (8855 : ℕ) :=
  (Nat.squarefree_mul (show Nat.Coprime 385 23 by decide)).mpr
    ⟨squarefree_385, (Nat.prime_iff.mp (by decide : Nat.Prime 23)).squarefree⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hFK : ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K)
include D hn hBC hodd hBV hFK

/-- The literal containing component cannot have squarefree order away
from two and a single odd prime. -/
theorem source_nonnormal_oddNormalizer_no_component_of_order
    {q a b c : ℕ} (hq : q.Prime) (hc : Squarefree c)
    (hcard : Nat.card (K ⧸ center K) ∣ 2 ^ a * q ^ b * c) : False := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  apply Perfect.no_doubled_odd_ranks_of_order S (K ⧸ center K) hq hc hcard
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_,_,_,_,_,hr⟩ :=
    source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
  exact (hr p hp ho).symm.le.trans (primeRank_subgroup_le p _)

/-- All alternating rows of Theorem B are excluded without an A₅ marking. -/
theorem source_nonnormal_oddNormalizer_no_placed_alternating_component
    {n : ℕ} (hn9 : n ≤ 9) (e : K ⧸ center K ≃* alternatingGroup (Fin n)) : False := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  apply Perfect.no_doubled_odd_ranks S (K ⧸ center K) Nat.prime_three
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨_,_,_,_,_,hr⟩ :=
      source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
    exact (hr p hp ho).symm.le.trans (primeRank_subgroup_le p _)
  · intro p hp ho hne
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_congr p e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n p hp
        (by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2))]
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have hodd := ho.not_two_dvd_nat
      omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))

/-- The two binary linear rows of Theorem B are excluded by their actual orders. -/
theorem source_nonnormal_oddNormalizer_no_placed_binary_linear_component
    {n : ℕ} (hn45 : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : NeZero n := ⟨by rcases hn45 with rfl | rfl <;> decide⟩
  have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) n
  rcases hn45 with rfl | rfl
  · norm_num [hF,Fin.prod_univ_succ] at hcard
    apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
      (q := 3) (a := 6) (b := 2) (c := 35) Nat.prime_three squarefree_35
    rw [Nat.card_congr e.toEquiv,hcard]
    decide
  · norm_num [hF,Fin.prod_univ_succ] at hcard
    apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
      (q := 3) (a := 10) (b := 2) (c := 1085) Nat.prime_three squarefree_1085
    rw [Nat.card_congr e.toEquiv,hcard]
    decide

/-- The binary symplectic-six row is excluded by its literal projective order. -/
theorem source_nonnormal_oddNormalizer_no_placed_binary_symplectic_component
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 9) (b := 4) (c := 35) Nat.prime_three squarefree_35
  rw [Nat.card_congr e.toEquiv]
  exact (card_quotient_dvd_card (center (Theory.SpecificGroups.SymplecticSix.Sp F))).trans
    (by rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hF]; decide)

/-- The small derived G₂ row is excluded by its certified order. -/
theorem source_nonnormal_oddNormalizer_no_placed_g2_derived_component
    (e : K ⧸ center K ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 5) (b := 3) (c := 7) Nat.prime_three (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree
  rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  decide

/-- The actual M11 model is excluded by its certified order. -/
theorem source_nonnormal_oddNormalizer_no_placed_m11_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M11) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 4) (b := 2) (c := 55) Nat.prime_three squarefree_55
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order]
  decide

/-- The actual M12 model is excluded by its certified order. -/
theorem source_nonnormal_oddNormalizer_no_placed_m12_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M12) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 6) (b := 3) (c := 55) Nat.prime_three squarefree_55
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order]
  decide

/-- The actual M22 model is excluded by its certified order. -/
theorem source_nonnormal_oddNormalizer_no_placed_m22_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M22) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 7) (b := 2) (c := 385) Nat.prime_three squarefree_385
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
  decide

/-- The actual M23 model is excluded by its certified order. -/
theorem source_nonnormal_oddNormalizer_no_placed_m23_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M23) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 7) (b := 2) (c := 8855) Nat.prime_three squarefree_8855
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
  decide

/-- The actual M24 model is excluded by its certified order. -/
theorem source_nonnormal_oddNormalizer_no_placed_m24_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M24) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 10) (b := 3) (c := 8855) Nat.prime_three squarefree_8855
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m24_order]
  decide

end CFSG.Quasithin.Chapter10
