module

public import Theory.GroupTheory.CentralBinaryCommutatorDuality

/-!
# F.9: coset geometries with b > 2 and m(V₁) = 1

The duality lemma F.9.7 is proved here from its precise local group-theoretic
inputs: U = U_H is elementary abelian, Q = Q_H and U are normal in H,
Z = V₁ has order two and is central in H, Z ≤ Q, and [Q,U] ≤ Z.
In the section's setup these inputs follow from F.9.1 and F.9.2.1. The theorem
uses the literal linear dual of U/C_U(Q), and retains both the commutator
formula and invariance under simultaneous conjugation. The latter is the
contragredient equivariance identity, since all quotient classes have
representatives.

The two centralizer quotients are paired by commutators with values in Z.
Removing both radicals makes this pairing perfect; finite binary duality
proves surjectivity. Centrality of Z gives conjugation invariance.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §F.9, Lemma F.9.7, printed p.321 (PDF p.332).
The remaining coset-geometry and classification results of §F.9 are not yet
asserted in this module.
-/

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterF
open Subgroup
open scoped commutatorElement
/-- Lemma F.9.7 from its central-commutator inputs: the actual centralizer
quotient is the linear dual over `ZMod 2`. The second identity expresses
H-equivariance on quotient representatives. -/
public theorem lemma_F_9_7
    {H : Type*} [Group H] [Finite H]
    (Q U Z : Subgroup H) [Q.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (hZQ : Z ≤ Q) (hZ : Z ≤ center H) (hcomm : ⁅Q, U⁆ ≤ Z)
    (hZcard : Nat.card Z = 2) :
    ∃ (eZ : Z ≃* Multiplicative (ZMod 2))
      (e : (Q ⧸ (centralizer (U : Set H)).subgroupOf Q) ≃*
        Multiplicative (Module.Dual (ZMod 2)
          (Additive (U ⧸ (centralizer (Q : Set H)).subgroupOf U)))),
      (∀ (q : Q) (u : U),
        (e (QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q) q)).toAdd
          (Additive.ofMul (QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U) u)) =
        (eZ ⟨⁅(q : H), (u : H)⁆, hcomm (commutator_mem_commutator q.property u.property)⟩).toAdd) ∧
      (∀ (h : H) (q : Q) (u : U),
        (e (QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q)
            ⟨h * q * h⁻¹, (inferInstance : Q.Normal).conj_mem q q.property h⟩)).toAdd
          (Additive.ofMul (QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U)
            ⟨h * u * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)) =
        (e (QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q) q)).toAdd
          (Additive.ofMul (QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U) u))) := by
  obtain ⟨eZ, e, he, hinv⟩ := exists_equivariant_central_binary_commutator_duality
    Q U Z hZQ hZ hcomm hZcard
  refine ⟨eZ, e.trans MonoidHom.binaryCharacterEquivLinearDual, ?_, ?_⟩
  · intro q u
    exact congrArg Multiplicative.toAdd (he q u)
  · intro h q u
    exact congrArg Multiplicative.toAdd (hinv h q u)
end CFSG.Quasithin.ChapterF
