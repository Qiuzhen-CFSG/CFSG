module
public import Theory.SpecificGroups.Classical.SeventeenFiveRank
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.PCoreNormalizerAction

/-!
# Five-rank restrictions on binary classical quintic actors

The split two-dimensional tori rule out degrees divisible by four in SL₃.
For Sp₄ and G₂ the split or quadratic norm-one product torus rules out every
even degree. At odd degree the actual G₂ order is prime to five; an
automorphism of order five therefore has field component of order five,
forcing five to divide that same field degree.

The embeddings, octonion model and inner-field automorphism description are
existing checked model APIs. Source application: Aschbacher--Smith 14.6.15,
printed p.1035. This is a necessary model restriction, not the terminal
marked-parabolic comparison. ATLAS model attribution remains in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.QuinticRankOne
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_dvd_pow_sub_one {n : ℕ} (hn : 4 ∣ n) : 5 ∣ 2^n-1 := by
  apply (ZMod.natCast_eq_zero_iff _ 5).mp
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  obtain ⟨k,rfl⟩ := hn
  rw [pow_mul,(by decide : (2 : ZMod 5)^4=1),one_pow,sub_self]

private theorem five_dvd_sub_or_add_of_even {n : ℕ} (hn : Even n) :
    5 ∣ 2^n-1 ∨ 5 ∣ 2^n+1 := by
  have hn2 : 2 ∣ n := even_iff_two_dvd.mp hn
  have hm : n%4=0 ∨ n%4=2 := by omega
  rcases hm with hm | hm
  · exact Or.inl (five_dvd_pow_sub_one (Nat.dvd_of_mod_eq_zero hm))
  · right
    apply (ZMod.natCast_eq_zero_iff _ 5).mp
    rw [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
      pow_eq_pow_mod _ (by decide : (2 : ZMod 5)^4=1),hm]
    decide

private theorem rank_of_product_embedding {C A : Type*} [Group C] [Finite C]
    [Group A] [Finite A] (h5 : 5 ∣ Nat.card C)
    (f : C × C →* A) (hf : Function.Injective f) : 2 ≤ primeRank 5 A := by
  have hr : 1 ≤ primeRank 5 C := by
    by_contra hh
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp (show primeRank 5 C = 0 by omega) h5
  have hi := Theory.GroupTheory.primeRank_le_of_injective 5 f hf
  rw [primeRank_prod_eq_add] at hi
  omega

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

/-- The split torus excludes field degrees divisible by four in SL₃. -/
theorem linear_degree (hF : Nat.card F = 2^n) (hr : primeRank 5 SL(3,F) ≤ 1) :
    ¬4 ∣ n := by
  intro hn
  have hh := Matrix.PSL3.SplitPrimeRank.special_rank F (hF ▸ five_dvd_pow_sub_one hn)
  omega

/-- Both quadratic tori are needed: symplectic five-rank one forces odd field degree. -/
theorem symplectic_degree [CharP F 2] (hF : Nat.card F = 2^n)
    (hr : primeRank 5 (Matrix.symplecticGroup (Fin 2) F) ≤ 1) : Odd n := by
  by_contra hn
  have hn := Nat.not_odd_iff_even.mp hn
  rcases five_dvd_sub_or_add_of_even hn with hm | hp
  · have hh : 2 ≤ primeRank 5 (Matrix.symplecticGroup (Fin 2) F) :=
      Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank
      (by decide : Nat.Prime 5) (hF ▸ hm)
    omega
  · obtain ⟨f,_,hc,hf,_,_⟩ :=
      Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.exists_nonsplit_product (F := F)
    have hh : 2 ≤ primeRank 5 (Matrix.symplecticGroup (Fin 2) F) :=
      rank_of_product_embedding (by rwa [hc,hF]) f hf
    omega

/-- Split and norm-one product tori force odd field degree in G₂ as well. -/
theorem g2_degree [CharP F 2] (hF : Nat.card F = 2^n)
    (hr : primeRank 5 (Atlas.G2.Model F) ≤ 1) : Odd n := by
  by_contra hn
  have hn := Nat.not_odd_iff_even.mp hn
  rcases five_dvd_sub_or_add_of_even hn with hm | hp
  · have hh := rank_of_product_embedding (C := Fˣ) (by rwa [Nat.card_units,hF])
      Atlas.G2.torusHom Atlas.G2.torusHom_injective
    omega
  · obtain ⟨f,_,hf,_,_⟩ :=
      Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.exists_nonsplit_product (F := F)
    have hh := rank_of_product_embedding
      (by rwa [Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.card_normOne,hF]) f hf
    omega

/-- At odd binary degree the G₂ order is prime to five. -/
theorem g2_five_not_dvd (hF : Nat.card F = 2^n) (hn : Odd n) :
    ¬5 ∣ Nat.card (Atlas.G2.Model F) := by
  rw [Atlas.G2.card_Model,hF]
  intro hd
  have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ (2^n)^2 := Nat.one_le_pow _ _ hq
  have h6 : 1 ≤ (2^n)^6 := Nat.one_le_pow _ _ hq
  have hz := (ZMod.natCast_eq_zero_iff _ 5).mpr hd
  push_cast [Nat.cast_sub h2,Nat.cast_sub h6] at hz
  rw [pow_eq_pow_mod _ (by decide : (2 : ZMod 5)^4=1)] at hz
  have hm2 : n%2=1 := Nat.odd_iff.mp hn
  have hm : n%4=1 ∨ n%4=3 := by omega
  rcases hm with hm | hm <;> rw [hm] at hz <;> revert hz <;> decide

/-- The surviving G₂ actor has a genuine field component of order five,
so five divides the same field degree. -/
theorem g2_quintic_field [CharP F 2] (hF : Nat.card F = 2^n)
    (hq : 2 < Nat.card F) (hr : primeRank 5 (Atlas.G2.Model F) ≤ 1)
    (a : MulAut (Atlas.G2.Model F)) (ha : orderOf a = 5) :
    Odd n ∧ 5 ∣ n ∧
      orderOf (Atlas.G2.LieAutomorphismExtensions.fieldComponent hq a) = 5 := by
  have hn := g2_degree hF hr
  have hi := MulAut.prime_order_not_inner_of_not_dvd_card a ha (g2_five_not_dvd hF hn)
  have ho : orderOf (Atlas.G2.LieAutomorphismExtensions.fieldComponent hq a) = 5 := by
    apply orderOf_eq_prime
    · rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]
    · intro hh
      obtain ⟨g,hg⟩ := (Atlas.G2.LieAutomorphismExtensions.fieldComponent_eq_one_iff hq a).mp hh
      exact hi ⟨g,hg.symm⟩
  refine ⟨hn,?_,ho⟩
  have hd := ho ▸ orderOf_dvd_natCard (Atlas.G2.LieAutomorphismExtensions.fieldComponent hq a)
  rwa [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF] at hd

end Theory.SpecificGroups.Classical.QuinticRankOne
