module
public import Theory.SpecificGroups.Quaternion.PresentationHom
public import Theory.SpecificGroups.SL2.BinaryTetrahedral

/-!
# Maps from the binary tetrahedral presentation

The quaternion relations and the two generator identities for its
order-three action define a homomorphism from Q8 semidirect C3. The
elements need only satisfy power relations: degenerate images are allowed.
The proof extends compatibility from the quaternion generators to their
normal forms and then to all three cyclic powers before using the
semidirect-product universal property.

Adapted from the action-extension part of the binaryTetrahedralEquiv_of_data
proof in GLS3 5.2.6. This lower interface supports nonsplit central covers
of PSL2(3) without assuming an order-two kernel or a faithful image.
-/

public section
namespace GLS3.Chapter5.SchurPresentation

theorem exists_binaryTetrahedral_hom {E : Type*} [Group E]
    (a b t : E) (ha : a ^ 4 = 1) (hb : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b) (ht : t ^ 3 = 1)
    (hconjA : t * a * t⁻¹ = b * a)
    (hconjB : t * b * t⁻¹ = a⁻¹) :
    ∃ F : (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →* E,
      F (SemidirectProduct.inl (QuaternionGroup.a 1)) = a ∧
      F (SemidirectProduct.inl (QuaternionGroup.xa 0)) = b ∧
      F (SemidirectProduct.inr (Multiplicative.ofAdd 1)) = t := by
  let phi := QuaternionGroup.liftOfRelations a b ha hb hba
  let psi := QuaternionGroup.cyclicPowerHom 3 t ht
  have hphiA : phi (QuaternionGroup.a 1) = a :=
    QuaternionGroup.liftOfRelations_a_one a b ha hb hba
  have hphiB : phi (QuaternionGroup.xa 0) = b :=
    QuaternionGroup.liftOfRelations_xa_zero a b ha hb hba
  have hactionOne (x : QuaternionGroup 2) :
      phi (q8Cycle x) = t * phi x * t⁻¹ := by
    let f : QuaternionGroup 2 →* E := phi.comp q8Cycle.toMonoidHom
    let g : QuaternionGroup 2 →* E :=
      (MulAut.conj t).toMonoidHom.comp phi
    have hA : f (QuaternionGroup.a 1) = g (QuaternionGroup.a 1) := by
      change phi (q8Cycle (QuaternionGroup.a 1)) =
        t * phi (QuaternionGroup.a 1) * t⁻¹
      rw [q8Cycle_a_one,
        show QuaternionGroup.xa 1 =
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 by decide,
        map_mul, hphiA, hphiB, hconjA]
    have hB : f (QuaternionGroup.xa 0) = g (QuaternionGroup.xa 0) := by
      change phi (q8Cycle (QuaternionGroup.xa 0)) =
        t * phi (QuaternionGroup.xa 0) * t⁻¹
      rw [q8Cycle_xa_zero,
        show QuaternionGroup.a 3 = (QuaternionGroup.a 1)⁻¹ by decide,
        map_inv, hphiA, hphiB, hconjB]
    have hfg : f = g := by
      apply DFunLike.ext _ _
      intro y
      rcases y with i | i
      · rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
        rw [map_pow, map_pow, hA]
      · have hxa : QuaternionGroup.xa i =
            QuaternionGroup.xa 0 * QuaternionGroup.a i := by
          rw [QuaternionGroup.xa_mul_a]
          simp
        rw [hxa, map_mul, map_mul, hB]
        rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
        rw [map_pow, map_pow, hA]
    exact DFunLike.congr_fun hfg x
  have haction (k : Multiplicative (ZMod 3)) (x : QuaternionGroup 2) :
      phi (q8C3Action k x) = psi k * phi x * (psi k)⁻¹ := by
    change ZMod 3 at k
    fin_cases k
    · change phi ((q8Cycle ^ 0) x) = psi 1 * phi x * (psi 1)⁻¹
      simp
    · change phi ((q8Cycle ^ 1) x) =
        psi (Multiplicative.ofAdd 1) * phi x *
          (psi (Multiplicative.ofAdd 1))⁻¹
      simpa [psi, QuaternionGroup.cyclicPowerHom_one] using hactionOne x
    · change phi (q8Cycle (q8Cycle x)) =
        psi (Multiplicative.ofAdd 2) * phi x *
          (psi (Multiplicative.ofAdd 2))⁻¹
      rw [show psi (Multiplicative.ofAdd 2) = t ^ 2 by
        simpa [psi] using QuaternionGroup.cyclicPowerHom_intCast 3 t ht 2]
      calc
        phi (q8Cycle (q8Cycle x)) =
            t * phi (q8Cycle x) * t⁻¹ := hactionOne (q8Cycle x)
        _ = t * (t * phi x * t⁻¹) * t⁻¹ := by rw [hactionOne]
        _ = t ^ 2 * phi x * (t ^ 2)⁻¹ := by
          rw [pow_two]
          group
  let F : (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →* E :=
    SemidirectProduct.lift phi psi (by
      intro k
      apply MonoidHom.ext
      intro x
      exact haction k x)
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa [F] using hphiA
  · simpa [F] using hphiB
  · simpa [F, psi] using QuaternionGroup.cyclicPowerHom_one 3 t ht

end GLS3.Chapter5.SchurPresentation
