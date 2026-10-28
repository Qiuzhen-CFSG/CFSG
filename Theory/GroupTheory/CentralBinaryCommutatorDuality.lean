module

public import Theory.ElementaryAbelian.BinaryPairingQuotientDuality
public import Theory.GroupAction.QuotientCommutatorPairing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Central binary commutators give equivariant duality

Let U be a finite elementary abelian two-subgroup, and suppose [Q,U] lies in
a central subgroup Z of order two contained in Q. The commutator pairing
identifies Q/C_Q(U) with the binary dual of U/C_U(Q). Its two radicals are
exactly the two centralizers. If Q and U are normal, simultaneous conjugation
fixes the pairing, so the resulting isomorphism is equivariant for the dual
action. Neither equal quotient orders nor surjectivity is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma F.9.7, p.321.
-/

open scoped IsMulCommutative

namespace Subgroup
open scoped commutatorElement
/-- The central commutator pairing identifies the centralizer quotients as duals. -/
public theorem exists_central_binary_commutator_duality
    {G : Type*} [Group G] [Finite G]
    (Q U Z : Subgroup G) [IsElementaryAbelian 2 U]
    [(centralizer (U : Set G)).subgroupOf Q |>.Normal]
    (hZQ : Z ≤ Q) (hZ : Z ≤ center G) (hcomm : ⁅Q, U⁆ ≤ Z)
    (eZ : Z ≃* Multiplicative (ZMod 2)) :
    ∃ e : (Q ⧸ (centralizer (U : Set G)).subgroupOf Q) ≃*
        ((U ⧸ (centralizer (Q : Set G)).subgroupOf U) →* Multiplicative (ZMod 2)),
      ∀ (q : Q) (u : U),
        e (QuotientGroup.mk' ((centralizer (U : Set G)).subgroupOf Q) q)
          (QuotientGroup.mk' ((centralizer (Q : Set G)).subgroupOf U) u) =
        eZ ⟨⁅(q : G), (u : G)⁆, hcomm (commutator_mem_commutator q.property u.property)⟩ := by
  classical
  have hbot : (⊥ : Subgroup G).subgroupOf Z = (⊥ : Subgroup Z) := by ext z; simp
  let : ((⊥ : Subgroup G).subgroupOf Z).Normal := hbot.symm ▸ inferInstance
  let e0 : (Z ⧸ (⊥ : Subgroup G).subgroupOf Z) ≃* Z :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let : IsMulCommutative (Z ⧸ (⊥ : Subgroup G).subgroupOf Z) :=
    ⟨⟨fun a b => (e0.trans eZ).injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩
  have hQZ : Q ≤ centralizer (Z : Set G) := by
    intro q _ z hz
    exact (mem_center_iff.mp (hZ hz) q).symm
  have hZU : ⁅Z, U⁆ ≤ ⊥ := by
    apply commutator_le.mpr
    intro z hz u _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp (hZ hz) u).symm
  let f : Q →* (U →* Multiplicative (ZMod 2)) :=
    (centralQuotientCommutatorPairing Q U Z ⊥ hZQ hQZ hcomm hZU).compr₂
      (e0.trans eZ).toMonoidHom
  have hf (q : Q) (u : U) : f q u =
      eZ ⟨⁅(q : G), (u : G)⁆, hcomm (commutator_mem_commutator q.property u.property)⟩ := by
    dsimp only [f]
    rw [MonoidHom.compr₂_apply, centralQuotientCommutatorPairing_apply]
    rfl
  have hone (q : Q) (u : U) : f q u = 1 ↔ Commute (q : G) (u : G) := by
    rw [hf, ← eZ.map_one, eZ.injective.eq_iff, Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm
  have hkerQ : f.ker = (centralizer (U : Set G)).subgroupOf Q := by
    ext q
    change f q = 1 ↔ (q : G) ∈ centralizer (U : Set G)
    constructor
    · intro h u hu
      exact ((hone q ⟨u, hu⟩).mp (congrArg (fun k : U →* Multiplicative (ZMod 2) => k ⟨u, hu⟩) h)).symm.eq
    · intro h
      apply MonoidHom.ext
      intro u
      exact (hone q u).mpr ((h u u.property).symm)
  have hkerU : f.flip.ker = (centralizer (Q : Set G)).subgroupOf U := by
    ext u
    change f.flip u = 1 ↔ (u : G) ∈ centralizer (Q : Set G)
    constructor
    · intro h q hq
      exact ((hone ⟨q, hq⟩ u).mp (congrArg (fun k : Q →* Multiplicative (ZMod 2) => k ⟨q, hq⟩) h)).eq
    · intro h
      apply MonoidHom.ext
      intro q
      exact (hone q u).mpr (h q q.property)
  obtain ⟨e, he⟩ := MonoidHom.exists_binary_pairing_quotient_duality f.flip
  let qU := QuotientGroup.quotientMulEquivOfEq hkerU.symm
  let dualTransport : ((U ⧸ f.flip.ker) →* Multiplicative (ZMod 2)) ≃*
      ((U ⧸ (centralizer (Q : Set G)).subgroupOf U) →* Multiplicative (ZMod 2)) := {
    toFun k := k.comp qU.toMonoidHom
    invFun k := k.comp qU.symm.toMonoidHom
    left_inv k := by ext u; simp
    right_inv k := by ext u; simp
    map_mul' _ _ := rfl }
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hkerQ.symm).trans
    (e.trans dualTransport), ?_⟩
  intro q u
  exact (he u q).trans (hf q u)
/-- For normal subgroups and a central target of order two, the centralizer
duality is invariant under simultaneous conjugation. This is equivariance for
the contragredient action on the dual. -/
public theorem exists_equivariant_central_binary_commutator_duality
    {H : Type*} [Group H] [Finite H]
    (Q U Z : Subgroup H) [Q.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (hZQ : Z ≤ Q) (hZ : Z ≤ center H) (hcomm : ⁅Q, U⁆ ≤ Z)
    (hZcard : Nat.card Z = 2) :
    ∃ (eZ : Z ≃* Multiplicative (ZMod 2))
      (e : (Q ⧸ (centralizer (U : Set H)).subgroupOf Q) ≃*
        ((U ⧸ (centralizer (Q : Set H)).subgroupOf U) →* Multiplicative (ZMod 2))),
      (∀ (q : Q) (u : U),
        e (QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q) q)
          (QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U) u) =
        eZ ⟨⁅(q : H), (u : H)⁆, hcomm (commutator_mem_commutator q.property u.property)⟩) ∧
      (∀ (h : H) (q : Q) (u : U),
        e (QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q)
            ⟨h * q * h⁻¹, (inferInstance : Q.Normal).conj_mem q q.property h⟩)
          (QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U)
            ⟨h * u * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩) =
        e (QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q) q)
          (QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U) u)) := by
  let eZ : Z ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hZcard (by simp)
  obtain ⟨e, he⟩ := exists_central_binary_commutator_duality Q U Z hZQ hZ hcomm eZ
  refine ⟨eZ, e, he, ?_⟩
  intro h q u
  rw [he, he]
  congr 1
  apply Subtype.ext
  change ⁅h * (q : H) * h⁻¹, h * (u : H) * h⁻¹⁆ = ⁅(q : H), (u : H)⁆
  rw [← conjugate_commutatorElement,
    mem_center_iff.mp (hZ (hcomm (commutator_mem_commutator q.property u.property))) h,
    mul_inv_cancel_right]
end Subgroup
