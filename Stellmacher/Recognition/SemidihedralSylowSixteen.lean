module

public import ABG.Basic
public import ABG.ChapterII.Section1.Center
public import Stellmacher.Recognition.CoreFreeSemidihedralCentralizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Sylow order sixteen from the actual GL2(3) centralizers

If a finite group has a supplied semidihedral Sylow two-subgroup and every
involution centralizer is isomorphic to GL2(3), that same Sylow subgroup
has order sixteen. This is the cardinal consequence of the source-three
centralizer recognition in the simple N2 branch. Neither simplicity nor
the N2 condition is needed again once the centralizer models are given.
The final corollary derives these models from the original simple N2
hypotheses and the triviality of all two-local odd cores.

Take the central involution in the supplied semidihedral presentation.
Its centralizer contains the whole supplied Sylow, whose restriction is
therefore a Sylow of the centralizer. The matrix cardinality formula gives
the centralizer order forty-eight, with two-part sixteen. The subgroup
restriction equivalence transports this cardinality back to the original
Sylow. Orders are used only for this calculation, not for group recognition.

Source: Alperin--Brauer--Gorenstein II.1 Lemma 1(v) and II.3 Proposition 3
at characteristic three, article pp.9 and 27 of
`refs/latex/alperin-brauer-gorenstein.tex`.
-/

namespace Stellmacher.Recognition
open ABG
universe u

/-- Actual GL2(3) involution centralizers force the supplied semidihedral
Sylow two-subgroup to have order sixteen. -/
public theorem sylow_card_sixteen_of_gl2_three_centralizers
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (hcentralizers : ∀ x : G, orderOf x = 2 →
      Nonempty (Subgroup.centralizer ({x} : Set G) ≃* GL2 3 1)) :
    Nat.card S = 16 := by
  obtain ⟨n, hn, _, a, b, ha, hb, hab, hgen⟩ := hS
  let z : S := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := QuasiDihedral.half_order_pow_orderOf hn ha
  have hzc : z ∈ Subgroup.center S :=
    QuasiDihedral.half_order_pow_mem_center hn a b ha hb hab hgen
  let C := Subgroup.centralizer ({(z : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc (⟨s, hs⟩ : S)))
  obtain ⟨e⟩ := hcentralizers z ((Subgroup.orderOf_coe z).trans hz)
  have hCcard : Nat.card C = 48 := by
    rw [Nat.card_congr e.toEquiv]
    let : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    rw [Matrix.card_GL_field]
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by decide)]
    norm_num
  let T := S.subtype hSC
  have hTcard : Nat.card T = 16 := by
    rw [T.card_eq_multiplicity, hCcard]
    rw [show 48 = 2 ^ 4 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
      Nat.prime_two.factorization, Nat.prime_three.factorization]
    norm_num
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv).symm.trans hTcard

/-- The odd-core-free semidihedral alternative in the simple N2 reduction
has Sylow order sixteen. -/
public theorem semidihedral_sylow_card_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) :
    Nat.card S = 16 := by
  exact sylow_card_sixteen_of_gl2_three_centralizers S hS
    (involutionCentralizer_equiv_gl2_three_of_simple_nTwo S hS hN hcore)

end Stellmacher.Recognition
