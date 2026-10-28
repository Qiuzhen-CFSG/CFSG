module
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Odd split-torus elements inverted by Suzuki involutions

Every nonidentity involutory automorphism of Sz(2^(2m+1)) is inner.
Involution fusion conjugates its inducing element to the Weyl involution,
which inverts a generator of the split torus. The resulting element has
odd order 2^(2m+1)-1, at least seven for every nondegenerate Suzuki group.

For application to components, cyclic odd Sylow transfer also identifies
any perfect central cover with trivial two-core with the Suzuki quotient.
The equivalence agrees with the supplied central quotient projection.

Sources: Huppert--Blackburn III, XI.3.3, XI.3.10(e), XI.3.12(e);
GLS IV, Chapter 4, Lemma 3.1(b); Aschbacher--Smith I.1.2 and the Suzuki
exclusion in the proof of 12.6.26, printed p.832 of refs/quasithin.pdf.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- The actual involutory automorphism inverts a generator of a conjugate split torus. -/
theorem involution_inverts_split_generator (m : ℕ) (hm : 0 < m)
    (a : MulAut (SuzukiMatrixGroup m)) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    ∃ x : SuzukiMatrixGroup m, orderOf x = 2 ^ (2 * m + 1) - 1 ∧ a x = x⁻¹ := by
  obtain ⟨b, hb, _⟩ := ZD.suzuki_involutoryAut_inner_and_twoRank m (by omega) a ha
  have hb2 : b ^ 2 = 1 := ZD.suzuki_conj_sq_eq_one m (by omega) b (hb ▸ ha)
  have hbne : b ≠ 1 := by
    intro h
    apply hne
    rw [hb,h,map_one]
  have hbo : orderOf b = 2 := orderOf_eq_prime hb2 hbne
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (suzuki_involutions_isConj m hm (suzukiWeyl m) b (suzukiWeyl_orderOf m) hbo)
  let := suzukiSplitTorus_isCyclic m hm
  obtain ⟨t, ht⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (SuzukiSplitTorus m))
  have hto : orderOf (t : SuzukiMatrixGroup m) = 2 ^ (2 * m + 1) - 1 :=
    (Subgroup.orderOf_coe t).trans
      ((orderOf_eq_card_of_zpowers_eq_top ht).trans (suzukiSplitTorus_card m hm))
  refine ⟨MulAut.conj g t, ((MulAut.conj g).orderOf_eq _).trans hto, ?_⟩
  rw [hb]
  change b * (MulAut.conj g) (t : SuzukiMatrixGroup m) * b⁻¹ = _
  have hg' : (MulAut.conj g) (suzukiWeyl m) = b := hg
  rw [← hg', ← map_inv, ← map_mul, ← map_mul, suzukiWeyl_inv,
    suzukiWeyl_conj_splitTorus, map_inv]

/-- Every nontrivial involutory Suzuki automorphism inverts an odd-order element of order greater than five. -/
theorem involution_inverts_large_odd (m : ℕ) (hm : 0 < m)
    (a : MulAut (SuzukiMatrixGroup m)) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    ∃ x : SuzukiMatrixGroup m, Odd (orderOf x) ∧ 5 < orderOf x ∧ a x = x⁻¹ := by
  obtain ⟨x,hx,hi⟩ := involution_inverts_split_generator m hm a ha hne
  refine ⟨x, ?_, ?_, hi⟩
  · rw [hx]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) (by decide)
  · rw [hx]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ 2*m+1 by omega)
    norm_num at hh
    omega

/-- The central quotient marking lifts to an equivalence when the perfect source has trivial two-core. -/
theorem equiv_of_suzuki_central_quotient {B : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] (hB : pCore 2 B = ⊥) (m : ℕ) (hm : 0 < m)
    (e : (B ⧸ center B) ≃* SuzukiMatrixGroup m) :
    ∃ e' : B ≃* SuzukiMatrixGroup m, ∀ b, e' b = e (QuotientGroup.mk' (center B) b) := by
  let q := QuotientGroup.mk' (center B)
  let f : PerfectCentralCovering.Cover B (SuzukiMatrixGroup m) :=
    { toMonoidHom := e.toMonoidHom.comp q
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
      isPerfect := inferInstance
      ker_le_center := by
        intro b hb
        apply (QuotientGroup.eq_one_iff b).mp
        exact e.injective (hb.trans (map_one e).symm) }
  let hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Sylow p (SuzukiMatrixGroup m), IsCyclic P := by
    intro p hp hp2 P
    let : Fact p.Prime := ⟨hp⟩
    exact suzukiSylow_isCyclic_of_ne_two hm hp2 P
  exact ⟨f.equivOfPCoreEqBotOfCyclicSylow hB hcyc,
    fun b => f.equivOfPCoreEqBotOfCyclicSylow_apply hB hcyc b⟩
end BenderSuzuki.MatrixGroups
