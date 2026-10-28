module
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Coordinates

/-!
# Transport of the complete marked M₁₀ geometry

A simultaneous permutation conjugacy of the nine-group and the two
transpositions transports the semidihedral complement, its ambient center,
the literal quaternion intersection, and the chosen involution. Normality of
the specified extension is the only global extension hypothesis used here.

Source: Aschbacher, A 2-local characterization of M12 (2003), 4.9–4.10,
pp.41–42. The conjugacy witness must be constructed from the source marking.
-/

@[expose] public section
namespace AlternatingSix.M10.LocalGeometry
open Subgroup ShadowLocal

/-- The simultaneous identification needed for the source markings. -/
structure PermutationAlignment (m : Marking) where
  permutation : Equiv.Perm (Fin 6)
  nine_eq : standardNine.map (MulAut.conj permutation).toMonoidHom = m.D
  z_eq : permutation * standardZ * permutation⁻¹ = m.z
  u_eq : permutation * standardU * permutation⁻¹ = m.u

/-- Inversion of the marked nine-group gives actual ambient normalization. -/
theorem marked_b_normalizes (m : Marking) :
    permutationAction (m.u * m.z) ∈ normalizer (nine m.D : Set AutA6) := by
  have hn : m.u * m.z ∈ normalizer (m.D : Set (Equiv.Perm (Fin 6))) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      change (m.u * m.z) * x * (m.u * m.z)⁻¹ ∈ m.D
      rw [m.b_inverts x hx]
      exact m.D.inv_mem hx
    · rw [card_map_of_injective (MulAut.conj (m.u * m.z)).injective]
  exact m.D.le_normalizer_map permutationAction (mem_map_of_mem _ hn)

/-- Two transpositions have an even product, so the marked b lies in the
literal extension stabilizer. This needs no complement calculation. -/
theorem marked_b_mem (m : Marking) : permutationAction (m.u * m.z) ∈ stabilizer m.D := by
  refine ⟨?_, marked_b_normalizes m⟩
  apply (show ShadowLocal.inner ≤ extension from le_sup_left)
  have he : m.u * m.z ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, m.u_swap.sign_eq, m.z_swap.sign_eq]
    decide
  exact ⟨⟨m.u * m.z, he⟩, (permutationAction_coe ⟨m.u * m.z, he⟩).symm⟩

namespace PermutationAlignment
variable {m : Marking} (a : PermutationAlignment m)

def automorphism : AutA6 ≃* AutA6 := MulAut.conj (permutationAction a.permutation)

theorem on_permutation (p : Equiv.Perm (Fin 6)) :
    a.automorphism (permutationAction p) =
      permutationAction (a.permutation * p * a.permutation⁻¹) := by
  simp only [automorphism, MulAut.conj_apply, map_mul, map_inv]

theorem nine_image : (nine standardNine).map a.automorphism.toMonoidHom = nine m.D := by
  have h : a.automorphism.toMonoidHom.comp permutationAction =
      permutationAction.comp (MulAut.conj a.permutation).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact a.on_permutation x
  rw [nine, map_map, h, ← map_map, a.nine_eq]
  rfl

theorem on_z : a.automorphism (permutationAction standardZ) = permutationAction m.z := by
  rw [a.on_permutation, a.z_eq]

theorem on_b : a.automorphism (permutationAction (standardU * standardZ)) =
    permutationAction (m.u * m.z) := by
  rw [map_mul, map_mul, a.on_permutation, a.on_permutation, a.u_eq, a.z_eq, map_mul]

theorem extension_image (hn : extension.Normal) :
    extension.map a.automorphism.toMonoidHom = extension := by
  let := hn
  exact Subgroup.Normal.map_conj_eq extension _

theorem stabilizer_image (hn : extension.Normal) :
    (stabilizer standardNine).map a.automorphism.toMonoidHom = stabilizer m.D := by
  rw [stabilizer, map_inf _ _ _ a.automorphism.injective, a.extension_image hn,
    map_equiv_normalizer_eq, a.nine_image]
  rfl

/-- Transport every local clause through the actual automorphism, including
the quaternion intersection and the involution's stabilizer exclusion. -/
noncomputable def localFacts (hn : extension.Normal) (l : LocalFacts standardMarking) :
    LocalFacts m where
  P := l.P.map a.automorphism.toMonoidHom
  card_P := (card_map_of_injective a.automorphism.injective).trans l.card_P
  semidihedral := by
    let e := l.P.equivMapOfInjective a.automorphism.toMonoidHom a.automorphism.injective
    obtain ⟨p, q, hp, hq, hr, hg⟩ := l.semidihedral
    refine ⟨e p, e q, (e.orderOf_eq p).trans hp, (e.orderOf_eq q).trans hq, ?_, ?_⟩
    · simpa only [map_mul, map_inv, map_pow] using congrArg e hr
    · have h := congrArg (Subgroup.map e.toMonoidHom) hg
      simpa only [Subgroup.map_sup, MonoidHom.map_zpowers,
        map_top_of_surjective e.toMonoidHom e.surjective, MulEquiv.coe_toMonoidHom] using h
  normalizer_eq := by
    have hl : normalizer (nine standardNine : Set AutA6) = nine standardNine ⊔ l.P :=
      l.normalizer_eq
    rw [← a.nine_image, ← map_equiv_normalizer_eq, hl, Subgroup.map_sup]
  disjoint := by
    rw [← a.nine_image]
    exact disjoint_map a.automorphism.injective l.disjoint
  z_mem := by
    rw [← a.on_z]
    exact mem_map_of_mem _ l.z_mem
  center_P := by
    rw [← map_embeddedCenter _ _ a.automorphism.injective, l.center_P,
      MonoidHom.map_zpowers]
    change zpowers (a.automorphism (permutationAction (standardU * standardZ))) = _
    rw [a.on_b]
  quaternion := by
    obtain ⟨e⟩ := l.quaternion
    have hi : (l.P ⊓ extension).map a.automorphism.toMonoidHom =
        l.P.map a.automorphism.toMonoidHom ⊓ extension := by
      rw [map_inf _ _ _ a.automorphism.injective, a.extension_image hn]
    exact ⟨(MulEquiv.subgroupCongr hi.symm).trans
      (((l.P ⊓ extension).equivMapOfInjective a.automorphism.toMonoidHom
        a.automorphism.injective).symm.trans e)⟩
  b_mem := marked_b_mem m
  r := a.automorphism l.r
  r_mem := by
    rw [← a.extension_image hn]
    exact mem_map_of_mem _ l.r_mem
  r_sq := by rw [← map_mul, l.r_sq, map_one]
  r_not_mem_P := by
    intro h
    exact l.r_not_mem_P ((mem_map_iff_mem a.automorphism.injective).mp h)
  r_not_mem_stabilizer := by
    rw [← a.stabilizer_image hn]
    intro h
    exact l.r_not_mem_stabilizer ((mem_map_iff_mem a.automorphism.injective).mp h)
  r_normalizes_P := l.P.le_normalizer_map a.automorphism.toMonoidHom
    (mem_map_of_mem _ l.r_normalizes_P)

end PermutationAlignment
end AlternatingSix.M10.LocalGeometry
