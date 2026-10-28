module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.CubeLine
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.CubeAction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.SylowCenter

/-!
# Nontrivial elementary monomial intersections

The cube-root line lies in each coordinate-sign derived centralizer. The
ambient three-rank forces it into the elementary subgroup once monomial
conjugation is known to fix or invert it. A coordinate-sign centralizer
centralizing the intrinsic Sylow center then gives the required intersection.

The final theorem discharges both geometric premises using the actual
projective coordinate action and the intrinsic center of the ambient Sylow.
The same rank argument handles elementary subgroups in the diagonal kernel
and those with a three-cycle image. The product-order hypothesis is retained
in the contract for the position assembly, although this argument needs only
the containment of the product in the monomial subgroup.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of refs/quasithin.pdf); GLS3, Theorem 6.5.3(b).
-/

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial

open Monomial Matrix.PSL3.OuterSolvable.OddPrimeCoverage

variable {F : Type*} [Field F]

/-- The concrete cube-root and rank calculations reduce the intersection to
monomial conjugation and the position of the actual intrinsic Sylow center. -/
theorem monomial_intersection_ne_bot_of_coordinate_calculations [Finite F]
    (hmod : Nat.card F % 3 = 1) (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F))
    (hU : IsElementaryAbelian 3 U) (hcard : Nat.card U = 9) (hrank : primeRank 3 PSL(3,F) = 2)
    (hUM : U ≤ Matrix.SL3.SplitMonomial.projective F)
    (hconj : ∀ a : Fˣ, orderOf a = 3 → ∀ g ∈ Matrix.SL3.SplitMonomial.projective F,
      g * cubeElement a * g⁻¹ = cubeElement a ∨ g * cubeElement a * g⁻¹ = (cubeElement a)⁻¹)
    (hpos : ∃ k : Fin 3, centralizer ({signElement (F := F) k} : Set PSL(3,F)) ≤
      centralizer ((center (T : Subgroup PSL(3,F))).map (T : Subgroup PSL(3,F)).subtype : Set PSL(3,F))) :
    (centralizerDerived (T : Subgroup PSL(3,F))).subgroupOf U ≠ ⊥ := by
  obtain ⟨a, ha⟩ := exists_unit_order_three hmod
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hmem := cubeElement_mem_elementary U hU hcard hrank a ha (fun u hu => hconj a ha u (hUM hu))
  obtain ⟨k, hk⟩ := hpos
  have hder : cubeElement a ∈ centralizerDerived (T : Subgroup PSL(3,F)) := by
    rw [centralizerDerived_eq_center]
    exact commutator_mono hk hk (cubeElement_mem_derived a ha3 k)
  intro hbot
  have hb : (⟨cubeElement a, hmem⟩ : U) ∈
      (centralizerDerived (T : Subgroup PSL(3,F))).subgroupOf U := hder
  rw [hbot] at hb
  have h1 : cubeElement a = 1 := congrArg Subtype.val (mem_bot.mp hb)
  have ha1 : a = 1 := cubeElement_injective (h1.trans (map_one (cubeHom (F := F))).symm)
  have ho : orderOf a = 1 := ha1 ▸ orderOf_one
  omega

/-- An elementary subgroup of order nine whose product with the ambient Sylow
lies in the projective monomial subgroup meets the derived centralizer of the
Sylow center nontrivially. Both coordinate premises are proved in the concrete
matrix quotient. -/
theorem monomial_intersection_ne_bot [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : p.Prime) (hodd : Odd p)
    (hlarge : 3 < p) (hmod : p % 3 = 1)
    (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F))
    (hU : IsElementaryAbelian 3 U) (hcard : Nat.card U = 9)
    (hrank : primeRank 3 PSL(3,F) = 2)
    (_hprod : Nat.card (U ⊔ (T : Subgroup PSL(3,F)) : Subgroup PSL(3,F)) = 9 * Nat.card T)
    (hmono : U ⊔ (T : Subgroup PSL(3,F)) ≤ Matrix.SL3.SplitMonomial.projective F) :
    (centralizerDerived (T : Subgroup PSL(3,F))).subgroupOf U ≠ ⊥ := by
  apply monomial_intersection_ne_bot_of_coordinate_calculations
    (by simpa only [hF] using hmod) T U hU hcard hrank (le_sup_left.trans hmono)
  · intro a ha g hg
    apply cubeElement_conj_eq_or_inv a ?_ g hg
    rw [← ha]
    exact pow_orderOf_eq_one a
  · exact sylow_center_coordinate_position hF hp hodd hlarge hmod T
      (le_sup_right.trans hmono)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
