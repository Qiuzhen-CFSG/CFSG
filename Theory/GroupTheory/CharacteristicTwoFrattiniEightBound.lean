module
public import Theory.PGroupCore
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.ElementaryEightAutomorphismBound

/-!
# A characteristic-two group with an elementary-eight Frattini quotient

Let K be a finite solvable group whose two-core Q is self-centralizing.
If Q/Φ(Q) has order eight and a supplied Sylow two-subgroup has order
twice that of Q, then K has order at most six times that of Q.

Conjugation on Q has two-group kernel by self-centralization. Burnside's
Frattini automorphism kernel theorem therefore makes the kernel of the
induced action on Q/Φ(Q) a normal two-group, hence a subgroup of Q.
Conversely, Q acts trivially on its abelian Frattini quotient, identifying
the kernel with Q. The action image is solvable, with Sylow two-subgroup
of order two. The elementary-eight automorphism bound gives image order
at most six, and multiplication by the kernel order proves the result.

This standard Burnside-Frattini action argument supplies the order-32
normalizer branch in Stellmacher (10.1)(a3), printed p.61 of
`refs/files/stellmacher-n-group.pdf`. The theorem has no campaign hypotheses.
-/

open scoped IsMulCommutative

/-- A self-centralizing two-core with elementary-eight Frattini quotient has
index at most six when its Sylow two-overgroup has relative order two. -/
public theorem card_le_six_mul_of_characteristic_two_frattini_eight
    {K : Type*} [Group K] [Finite K] [Group.IsSolvable K]
    (P : Sylow 2 K)
    (hchar : Subgroup.centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hFrattini : Nat.card (pCore 2 K ⧸ frattini (pCore 2 K)) = 8)
    (hSylow : Nat.card P = 2 * Nat.card (pCore 2 K)) :
    Nat.card K ≤ 6 * Nat.card (pCore 2 K) := by
  classical
  let Q := pCore 2 K
  have hQ : IsPGroup 2 Q := pCore_isPGroup
  let _ : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let V := Q ⧸ frattini Q
  let _ : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let conjugation : K →* MulAut Q := MulAut.conjNormal
  let action : K →* MulAut V := (Subgroup.quotientAut (frattini Q)).comp conjugation
  have hconjker : conjugation.ker ≤ Q := by
    intro g hg
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hfix := congrArg (fun f : MulAut Q => (f ⟨q, hq⟩ : K))
      (MonoidHom.mem_ker.mp hg)
    change g * q * g⁻¹ = q at hfix
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hkernel : IsPGroup 2 action.ker :=
    (Subgroup.isPGroup_quotientAut_frattini_kernel hQ).comap_of_ker_isPGroup
      conjugation (hQ.to_le hconjker)
  have hker_le : action.ker ≤ pCore 2 K := le_sSup ⟨inferInstance, hkernel⟩
  have hker : action.ker = Q := by
    apply le_antisymm hker_le
    intro g hg
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro v
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) v
    change Subgroup.quotientAut (frattini Q) (conjugation g)
      (QuotientGroup.mk' (frattini Q) q) = QuotientGroup.mk' (frattini Q) q
    rw [Subgroup.quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini Q)
      ((⟨g, hg⟩ : Q) * q * (⟨g, hg⟩ : Q)⁻¹) = QuotientGroup.mk' (frattini Q) q
    rw [map_mul, map_mul, map_inv,
      mul_comm (QuotientGroup.mk' (frattini Q) (⟨g, hg⟩ : Q))
        (QuotientGroup.mk' (frattini Q) q), mul_inv_cancel_right]
  have hfactor : Nat.card Q * Nat.card action.range = Nat.card K := by
    rw [← Subgroup.index_ker, hker]
    exact Q.card_mul_index
  let _ : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective action.rangeRestrict_surjective
  have himage : Nat.card action.range ≤ 6 := by
    apply card_le_six_of_elementary_eight_automorphisms V hFrattini action.range
    let imageSylow := P.mapSurjective action.rangeRestrict_surjective
    refine ⟨imageSylow, ?_⟩
    have hQP : Q ≤ P := hQ.le_sylow_of_normal P
    have hsubcard : Nat.card (Q.subgroupOf (P : Subgroup K)) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    have hmul := (Q.subgroupOf (P : Subgroup K)).card_mul_index
    rw [hsubcard, hSylow] at hmul
    have hindex : (Q.subgroupOf (P : Subgroup K)).index = Nat.card imageSylow := by
      have hrel := Subgroup.relIndex_ker (K := (P : Subgroup K)) action.rangeRestrict
      rw [MonoidHom.ker_rangeRestrict, hker] at hrel
      exact hrel
    rw [hindex] at hmul
    have hpos : 0 < Nat.card Q := Nat.card_pos
    nlinarith
  rw [← hfactor]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.card Q) himage
