module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Transport of left-coset actions under a group isomorphism

The map gH ↦ e(g)e(H) is an equivariant equivalence of the literal left-coset
spaces. Consequently, two-transitivity of the image subgroup's coset action
transports to the original group. No subgroup normality is assumed.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.4.12(2), printed p.97 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

noncomputable def cosetEquivMap (e : G ≃* K) (H : Subgroup G) :
    G ⧸ H ≃ K ⧸ H.map e.toMonoidHom :=
  Quotient.congr e.toEquiv (by
    intro a b
    simp only [QuotientGroup.leftRel_apply]
    change a⁻¹ * b ∈ H ↔ (e a)⁻¹ * e b ∈ H.map e.toMonoidHom
    rw [← map_inv, ← map_mul]
    simp only [Subgroup.mem_map_equiv, e.symm_apply_apply])

theorem cosetEquivMap_smul (e : G ≃* K) (H : Subgroup G) (g : G) (q : G ⧸ H) :
    cosetEquivMap e H (g • q) = e g • cosetEquivMap e H q := by
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (fun x : K => (QuotientGroup.mk x : K ⧸ H.map e.toMonoidHom)) (e.map_mul g x)

theorem two_pretransitive_of_map (e : G ≃* K) (H : Subgroup G)
    (ht : MulAction.IsMultiplyPretransitive K (K ⧸ H.map e.toMonoidHom) 2) :
    MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  let f := cosetEquivMap e H
  obtain ⟨k, hka, hkb⟩ := MulAction.is_two_pretransitive_iff.mp ht
    (f.injective.ne hab) (f.injective.ne hcd)
  refine ⟨e.symm k, f.injective ?_, f.injective ?_⟩
  · simpa only [f, cosetEquivMap_smul, e.apply_symm_apply] using hka
  · simpa only [f, cosetEquivMap_smul, e.apply_symm_apply] using hkb

end Subgroup
