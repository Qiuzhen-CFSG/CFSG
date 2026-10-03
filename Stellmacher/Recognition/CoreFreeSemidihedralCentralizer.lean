module
public import ABG.ChapterII.Section3.SourceThreeSemidihedralModel
public import Stellmacher.Recognition.SourceCharacteristicThree
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Actual involution centralizers in the core-free-local semidihedral N2 branch

Let G be finite simple with a supplied semidihedral Sylow two-subgroup S.
Assume G is N2 and every two-local subgroup has trivial odd core. Then the
centralizer of every actual involution x is isomorphic to GL2(3). The same
isomorphism gives the existing ABG characteristic parameters q=3,d=1 by
taking the trivial central quotient kernel. These are derived local
conclusions, not assumptions about the final ABG main theorem.

The QD fusion theorem makes all involutions conjugate. Conjugate the central
involution of S to x and transport S along that same conjugation. The
resulting semidihedral Sylow lies in C_G(x), proving the required Sylow
shape without a new local hypothesis. This centralizer is itself two-local,
so the original odd-core hypothesis applies to it. The source characteristic
three theorem supplies its actual characteristic SL2 datum, and the proved
core-free Q model gives the actual GL2 equivalence. Both supplied Sylow
geometry and involution x are retained throughout.

Source: ABG II.1 QD fusion, II.2 Proposition 1, and II.3 Proposition 3 at
q=3, together with the N2 condition and the trivial-odd-core local reduction
in Stellmacher's theorem-two preamble. No ABG or Stellmacher classification
placeholder is used. Global recognition as PSL3(3) or M11 is subsequent.
-/

namespace Stellmacher.Recognition
open ABG
universe u

public theorem involutionCentralizer_equiv_gl2_three_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥)
    (x : G) (hx : orderOf x = 2) :
    Nonempty ((Subgroup.centralizer ({x} : Set G)) ≃* GL2 3 1) := by
  classical
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hS0 := hS
  obtain ⟨n, hn, _, a, b, ha, hb, hab, hgen⟩ := hS
  let z : S := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := QuasiDihedral.half_order_pow_orderOf hn ha
  have hzc : z ∈ Subgroup.center S :=
    QuasiDihedral.half_order_pow_mem_center hn a b ha hb hab hgen
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hzi⟩ := hcov z ((Subgroup.orderOf_coe z).trans hz)
  obtain ⟨j, hxj⟩ := hcov x hx
  have hzx : IsConj (z : G) x := hzi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hzx
  let e := S.equivSMul g
  have hT : IsSemidihedralGroup (g • S : Sylow 2 G) := semidihedral_equiv e hS0
  have hzc' : e z ∈ Subgroup.center (g • S : Sylow 2 G) := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨s, rfl⟩ := e.surjective t
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hzc s)
  have he : ((e z : (g • S : Sylow 2 G)) : G) = x := hg
  let C := Subgroup.centralizer ({x} : Set G)
  have hTC : ((g • S : Sylow 2 G) : Subgroup G) ≤ C := by
    intro t ht
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc' (⟨t, ht⟩ : (g • S : Sylow 2 G)))
    change t * (e z).val = (e z).val * t at hh
    simpa only [he] using hh
  let T := (g • S : Sylow 2 G).subtype hTC
  let eT : T ≃* (g • S : Sylow 2 G) := Subgroup.subgroupOfEquivOfLe hTC
  have hCS : HasQuasiDihedralSylowTwoSubgroups C := ⟨T, semidihedral_equiv eT.symm hT⟩
  have hCcore : pPrimeCore 2 C = ⊥ := hcore C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hx)
  have hq := (sourceCharacteristicPower_three_of_simple_nTwo ⟨S, hS0⟩ hN).at_involution hQD x hx
  exact qGroup_equiv_gl2_three_of_corefree_semidihedral
    (qd_involutionCentralizer_isQGroup hQD x hx).1 hCcore hCS hq

public theorem involutionCentralizerParameters_three_one_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥)
    (x : G) (hx : orderOf x = 2) : InvolutionCentralizerParameters x 3 1 := by
  obtain ⟨e⟩ := involutionCentralizer_equiv_gl2_three_of_simple_nTwo S hS hN hcore x hx
  refine ⟨3, 1, Nat.prime_three, by decide, by decide, Or.inl ⟨by decide, ?_⟩⟩
  exact ⟨⊥, inferInstance, bot_le, by simp, by simp,
    ⟨e.trans QuotientGroup.quotientBot.symm⟩⟩

end Stellmacher.Recognition
