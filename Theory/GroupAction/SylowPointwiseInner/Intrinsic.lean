module

public import Theory.GroupAction.SylowPointwiseInner.Ambient
public import Theory.GroupAction.SylowPointwiseInnerTransport

/-!
# Intrinsic Sylow fixers in a normal subgroup

If the centralizer of a normal subgroup L is trivial, an ambient element
whose action on L is inner already belongs to L. A pointwise-inner theorem
for the literal Sylow subgroup of L supplies this inner action. No ambient
Sylow subgroup or extension of the given Sylow is required.

The application in Aschbacher--Smith 13.5.21 identifies the full actor group
with its marked component when the remaining generator fixes a Sylow of
that component. Actual matrix and exceptional models enter only through
an equivalence carrying the pointwise-inner theorem.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {E : Type*} [Group E]

/-- A fixer of an intrinsic Sylow belongs to the self-centralizing normal
subgroup when every such automorphism is inner. -/
theorem mem_normal_of_centralizes_intrinsic_sylow
    (L : Subgroup E) [L.Normal]
    (hfaith : centralizer (L : Set E) = ⊥)
    (hinner : ∀ (P : Sylow 2 L) (a : MulAut L),
      (∀ x ∈ P, a x = x) → ∃ z ∈ P, a = MulAut.conj z)
    (P : Sylow 2 L) (t : E)
    (hc : ∀ x ∈ P, (x : E) * t = t * (x : E)) : t ∈ L := by
  obtain ⟨z, _, hz⟩ := hinner P (MulAut.conjNormal t) (by
    intro x hx
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hc x hx, mul_inv_cancel_right])
  have ht : t = (z : E) :=
    MulAut.conjNormal_injective_of_centralizer_eq_bot L hfaith
      (hz.trans MulAut.conjNormal_val.symm)
  exact ht ▸ z.property

/-- Model transport for the same actual ambient element and intrinsic Sylow. -/
theorem mem_normal_of_centralizes_intrinsic_sylow_of_equiv [Finite E]
    {M : Type*} [Group M] (L : Subgroup E) [L.Normal]
    (hfaith : centralizer (L : Set E) = ⊥) (e : L ≃* M)
    (hinner : ∀ (P : Sylow 2 M) (a : MulAut M),
      (∀ x ∈ P, a x = x) → ∃ z ∈ P, a = MulAut.conj z)
    (P : Sylow 2 L) (t : E)
    (hc : ∀ x ∈ P, (x : E) * t = t * (x : E)) : t ∈ L :=
  mem_normal_of_centralizes_intrinsic_sylow L hfaith
    (MulAut.fixing_sylow_inner_of_equiv e hinner) P t hc

/-- A Sylow-central generator adds nothing to the marked normal subgroup. -/
theorem normal_eq_top_of_intrinsic_sylow_generator [Finite E]
    {M : Type*} [Group M] (L : Subgroup E) [L.Normal]
    (hfaith : centralizer (L : Set E) = ⊥) (e : L ≃* M)
    (hinner : ∀ (P : Sylow 2 M) (a : MulAut M),
      (∀ x ∈ P, a x = x) → ∃ z ∈ P, a = MulAut.conj z)
    (P : Sylow 2 L) (t : E)
    (hc : ∀ x ∈ P, (x : E) * t = t * (x : E))
    (hgen : L ⊔ zpowers t = ⊤) : L = ⊤ := by
  have ht := mem_normal_of_centralizes_intrinsic_sylow_of_equiv L hfaith e hinner P t hc
  rw [sup_eq_left.mpr ((zpowers_le).mpr ht)] at hgen
  exact hgen

end Theory.GroupTheory
