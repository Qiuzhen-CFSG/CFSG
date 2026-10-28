module

public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The canonical representation on an elementary binary section

Conjugation on the literal S/E quotient descends through an actor map
whose kernel is S. Its kernel acts by inner automorphisms on the abelian
quotient, so the representation requires no recognition or action witness.
The coordinate homomorphism is the original quotient map.

This supplies the actual binary section in G.2.3(6) and 12.8.9(2–3).
-/

open Subgroup
open scoped IsMulCommutative

namespace Representation.BinaryConjugationSection

private def representationOfBinaryAut
    {D Q : Type*} [Group D] [Group Q] [IsElementaryAbelian 2 Q]
    (β : D →* MulAut Q) : Representation (ZMod 2) D (Additive Q) where
  toFun a := (β a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change β 1 v.toMul = v.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change β (a * b) v.toMul = β a (β b v.toMul)
    rw [map_mul]
    rfl

/-- The binary coordinates and descended representation are constructed on
the actual subgroup quotient; the quotient map is retained literally. -/
public theorem exists_canonical
    {G D : Type*} [Group G] [Group D]
    (H S E : Subgroup G) (hSH : S ≤ H) (hES : E ≤ S)
    (hNS : H ≤ normalizer (S : Set G)) (hNE : H ≤ normalizer (E : Set G))
    [(E.subgroupOf S).Normal] [IsElementaryAbelian 2 (S ⧸ E.subgroupOf S)]
    (π : H →* D) (hπ : Function.Surjective π) (hk : π.ker = S.subgroupOf H) :
    ∃ (σ : Representation (ZMod 2) D (Additive (S ⧸ E.subgroupOf S)))
      (d : Representation.BinaryConjugationSection H S E (σ.comp π)),
      ∀ s : S, (d.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' (E.subgroupOf S) s) := by
  let Q := S ⧸ E.subgroupOf S
  let q := QuotientGroup.mk' (E.subgroupOf S)
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action H S E hNS hNE inferInstance
  have hkill : π.ker ≤ α.ker := by
    intro h hh
    have hhS : (h : G) ∈ S := by
      change h ∈ S.subgroupOf H
      rwa [← hk]
    apply MonoidHom.mem_ker.mpr
    ext v
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf S) v
    rw [hα]
    change q ((⟨h, hhS⟩ : S) * s * (⟨h, hhS⟩ : S)⁻¹) = q s
    simp only [map_mul, map_inv]
    rw [mul_comm (q ⟨h, hhS⟩) (q s), mul_inv_cancel_right]
  let β : D →* MulAut Q := π.liftOfSurjective hπ ⟨α, hkill⟩
  have hβ (h : H) : β (π h) = α h :=
    π.liftOfRightInverse_comp_apply (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨α, hkill⟩ h
  let σ := representationOfBinaryAut β
  let c : S →* Multiplicative (Additive Q) := {
    toFun := fun s => Multiplicative.ofAdd (Additive.ofMul (q s))
    map_one' := q.map_one
    map_mul' := q.map_mul }
  have honto : Function.Surjective c := by
    intro v
    obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective (E.subgroupOf S) v.toAdd.toMul
    exact ⟨s, hs⟩
  have hker : c.ker = E.subgroupOf S := by
    ext s
    exact QuotientGroup.eq_one_iff s
  let d : Representation.BinaryConjugationSection H S E (σ.comp π) := {
    section_le := hSH
    kernel_le := hES
    normalized := hNS
    coordinates := c
    onto := honto
    kernel_eq := hker
    equivariant := by
      intro h s
      change q _ = β (π h) (q s)
      rw [hβ]
      exact (hα h s).symm }
  exact ⟨σ, d, fun _ => rfl⟩

end Representation.BinaryConjugationSection
