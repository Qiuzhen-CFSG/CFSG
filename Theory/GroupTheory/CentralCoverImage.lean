module
public import Mathlib.GroupTheory.Index

/-!
# Images over central quotient maps

An image which surjects modulo a central kernel generates the whole group
together with that kernel and is normal. For an injective source map, the
intersection of the image with the quotient kernel is isomorphic to the
kernel of the composite map, so their cardinalities agree.

The generation proof writes every element as a kernel element times an
image element. Both factors normalize the image, giving normality. The
kernel intersection is the actual subgroup image under the injection.
This supplies the final subgroup extraction in central-cover recognition,
including ABG II.3 Proposition 2.
-/

namespace MonoidHom

public theorem range_data_of_central_ker {B E Q : Type*}
    [Group B] [Group E] [Group Q] (q : E →* Q) (f : B →* E)
    (hcenter : q.ker ≤ Subgroup.center E)
    (hsurj : Function.Surjective (q.comp f)) (hinj : Function.Injective f) :
    q.ker ⊔ f.range = ⊤ ∧ f.range.Normal ∧
      Nat.card ↥(q.ker ⊓ f.range) = Nat.card (q.comp f).ker := by
  have htop : q.ker ⊔ f.range = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨b, hb⟩ := hsurj (q x)
    have hk : x * (f b)⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, show q (f b) = q x from hb]
      exact mul_inv_cancel _
    have hr : f b ∈ f.range := ⟨b, rfl⟩
    have h := (q.ker ⊔ f.range).mul_mem
      ((show q.ker ≤ q.ker ⊔ f.range from le_sup_left) hk)
      ((show f.range ≤ q.ker ⊔ f.range from le_sup_right) hr)
    simpa using h
  have hn : f.range.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← htop]
    exact sup_le (hcenter.trans (Subgroup.center_le_normalizer _)) f.range.le_normalizer
  have himage : (q.comp f).ker.map f = q.ker ⊓ f.range := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨hb, ⟨b, rfl⟩⟩
    · rintro ⟨hx, b, rfl⟩
      exact ⟨b, hx, rfl⟩
  refine ⟨htop, hn, ?_⟩
  rw [← himage]
  exact (Nat.card_congr ((q.comp f).ker.equivMapOfInjective f hinj).toEquiv).symm

end MonoidHom
