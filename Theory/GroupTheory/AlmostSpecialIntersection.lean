module
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Intersections of almost-special two-subgroups

A derived-subgroup bound on two generators extends to their intersection
against the generated group, provided the target layer is invariant.
For finite two-subgroups, disjoint bounds on their conjugate Frattini
images force the intersection to be elementary abelian. The proofs use
commutator preimages and functoriality of the Frattini subgroup.

These are the group-theoretic layer steps in Aschbacher–Smith,
G.2.3(4–5), combined manuscript of 1 March 2004, printed p.333.
-/

open Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

/-- The intersection is central modulo an invariant common derived bound. -/
public theorem intersection_commutator_sup_le {A B V : Subgroup G}
    (hAV : ⁅A, A⁆ ≤ V) (hBV : ⁅B, B⁆ ≤ V)
    (hnorm : A ⊔ B ≤ normalizer (V : Set G)) :
    ⁅A ⊓ B, A ⊔ B⁆ ≤ V := by
  have hA : A ≤ commutatorPreimage (A ⊔ B) (A ⊓ B) V :=
    le_commutatorPreimage le_sup_left
      ((commutator_mono le_rfl inf_le_left).trans hAV)
  have hB : B ≤ commutatorPreimage (A ⊔ B) (A ⊓ B) V :=
    le_commutatorPreimage le_sup_right
      ((commutator_mono le_rfl inf_le_right).trans hBV)
  rw [commutator_comm]
  exact (commutator_mono (sup_le hA hB) le_rfl).trans
    (commutator_commutatorPreimage_le (A ⊔ B) (A ⊓ B) V hnorm)

/-- Disjoint conjugate Frattini bounds make the literal intersection elementary. -/
public theorem conjugate_intersection_elementary [Finite G] {A Z : Subgroup G}
    (hp : IsPGroup 2 A) (hf : (frattini A).map A.subtype ≤ Z) (g : G)
    (hdis : Disjoint Z (Z.map (MulAut.conj g).toMonoidHom)) :
    IsElementaryAbelian 2 (A ⊓ A.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let f := (MulAut.conj g).toMonoidHom
  have hf' : (frattini (A.map f)).map (A.map f).subtype ≤ Z.map f := by
    rw [frattini_image_map A f (MulAut.conj g).injective]
    exact map_mono hf
  have he := frattini_eq_bot_of_disjoint_images hp (hp.map f)
    (show A ⊓ A.map f ≤ A from inf_le_left) inf_le_right
    (hdis.mono hf hf')
  let : Fact (IsPGroup 2 (A ⊓ A.map f : Subgroup G)) :=
    ⟨hp.of_injective (inclusion inf_le_left) (inclusion_injective _)⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp he

/-- An ambient Frattini bound also bounds the ambient commutator subgroup. -/
public theorem derived_le_of_frattini_image_le [Finite G] {A Z : Subgroup G}
    (hp : IsPGroup 2 A) (hf : (frattini A).map A.subtype ≤ Z) : ⁅A, A⁆ ≤ Z := by
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  have h := map_mono (f := A.subtype) (commutator_le_frattini_of_isPGroup (p := 2))
  rw [map_subtype_commutator] at h
  exact h.trans hf
end Subgroup
