module
public import Theory.Representation.BinaryOffender.QuadraticPairPermutation
public import Theory.Representation.BinaryOffender.DihedralProductDisplacement
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.Involutions

/-!
# Quadratic actors in a quintic pair without an index assumption

An elementary quadratic actor interchanging disjoint four-dimensional
summands would have rank one and fixed codimension at least four, violating
its quadratic-member bound. It therefore preserves both summands and actors.
The involution calculation and self-centralization place it in the dihedral
product, which has elementary two-rank at most two.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032. The application to
the actual ratio factors is in `QuinticGeometryParallel.Source`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
/-- The quadratic-member bound forbids interchange of a faithful pair of
four-dimensional summands; no index of the factor join is assumed. -/
theorem quadratic_preserves_pair
    (ρ : Representation (ZMod 2) G V) (I J : Submodule (ZMod 2) V)
    (hf : ∀ g : G, (∀ v ∈ I ⊔ J, ρ g v = v) → g = 1)
    (hd : Disjoint I J) (hI : Module.finrank (ZMod 2) I = 4)
    (hperm : ∀ g : G,
      (I.map (ρ g) = I ∧ J.map (ρ g) = J) ∨
      (I.map (ρ g) = J ∧ J.map (ρ g) = I))
    (B : Subgroup G) [IsElementaryAbelian 2 B]
    (hq : IsQuadratic ρ B) (hbound : fixedCodim ρ B ≤ 2 * rank B) :
    ∀ g ∈ B, I.map (ρ g) = I ∧ J.map (ρ g) = J := by
  intro g hg
  rcases hperm g with hkeep | hswap
  · exact hkeep
  · have hn : I ≠ ⊥ := by intro he; rw [he,finrank_bot] at hI; omega
    have hp (b : G) (_hb : b ∈ B) : I.map (ρ b) = I ∨ I.map (ρ b) = J :=
      (hperm b).imp And.left And.left
    obtain ⟨_,hr⟩ := quadratic_swapping_actor_rank ρ I J hf B hq hd hn hp g hg hswap
    have hl := finrank_le_fixedCodim_of_disjoint_map ρ I hg (by rw [hswap.1]; exact hd)
    have hu := hbound
    rw [hr] at hu
    rw [hI] at hl
    omega

omit [Finite G] in
/-- A preserving elementary actor lies in the self-centralizing product
of its two D10 factors. Elements of order four may still lie outside. -/
theorem elementary_preserving_le_quintic_join
    (A B C : Subgroup G) [IsElementaryAbelian 2 C]
    (eA : A ≃* DihedralGroup 5) (eB : B ≃* DihedralGroup 5)
    (hc : ∀ x ∈ A, ∀ y ∈ B, Commute x y)
    (hz : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ A ⊔ B)
    (hA : C ≤ normalizer (A : Set G)) (hB : C ≤ normalizer (B : Set G)) :
    C ≤ A ⊔ B := by
  intro g hg
  exact quintic_preserving_involution_mem_join A B eA eB hc hz g (hA hg) (hB hg)
    (elemPow_eq_one_of_isElementaryAbelian g hg)

/-- The literal product D10 × D10 bounds the elementary actor rank. -/
theorem elementary_rank_le_two_of_quintic_join
    (A B C : Subgroup G) [IsElementaryAbelian 2 C]
    (eA : A ≃* DihedralGroup 5) (eB : B ≃* DihedralGroup 5)
    (hd : Disjoint A B) (hc : ∀ x ∈ A, ∀ y ∈ B, Commute x y)
    (hC : C ≤ A ⊔ B) : rank C ≤ 2 := by
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    A B hd (fun x hx y hy => (hc x hx y hy).symm)
  have hsize : Nat.card (A ⊔ B : Subgroup G) = 100 := by
    rw [← Nat.card_congr e.toEquiv,Nat.card_prod,
      Nat.card_congr eA.toEquiv,Nat.card_congr eB.toEquiv,DihedralGroup.nat_card]
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 C).exists_card_eq
  have hdiv := card_dvd_of_le hC
  rw [hn,hsize] at hdiv
  have hn2 : n ≤ 2 := by
    by_contra! hh
    have h8 : 8 ∣ 100 := (Nat.pow_dvd_pow 2 hh).trans hdiv
    norm_num at h8
  simpa only [rank,hn,Nat.log_pow (by decide : 1 < 2)] using hn2

end CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel
