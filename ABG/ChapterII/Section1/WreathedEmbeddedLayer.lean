module
public import ABG.ChapterII.Section1.WreathedOvergroupExtension

/-!
# Wreathed quaternion-layer data through an actual embedding

Suppose a group R embeds in a wreathed group of height n and the image of
a subgroup A is the presentation's designated largest quaternion subgroup.
Then A has order 2^(n+1), and the center of R has order 2^(r+1) for some
r<n. Either A and that center generate R, or the embedding is surjective,
r=n−1, their join has index two, and an actual exterior element has square
generating the center.

Apply the established overgroup theorem to the actual image of R. The
injective map identifies its center, joins, relative indices and cyclic
subgroups; the exterior witness is pulled back through that same map.
No field model or Sylow shape of R is assumed.

This is the transport needed in Alperin--Brauer--Gorenstein II.3
Proposition 3, article p26, after identifying the embedded quaternion layer
with the Sylow intersection of the supplied normal SL2 subgroup. The
cardinality fixes the field two-part, and the exterior square data supplies
the subsequent index-two matrix-model comparison.
-/

namespace ABG.Wreathed.Presentation

public theorem embedded_quaternion_layer_data
    {S R : Type*} [Group S] [Group R] {n : ℕ} (P : Presentation S n)
    (f : R →* S) (hf : Function.Injective f) (A : Subgroup R)
    (hA : A.map f = P.Y) :
    Nat.card A = 2 ^ (n + 1) ∧
      ∃ r < n, Nat.card (Subgroup.center R) = 2 ^ (r + 1) ∧
        (A ⊔ Subgroup.center R = ⊤ ∨
          (Function.Surjective f ∧ r = n - 1 ∧ (A ⊔ Subgroup.center R).index = 2 ∧
            ∃ a : R, a ∉ A ⊔ Subgroup.center R ∧
              Subgroup.zpowers (a ^ 2) = Subgroup.center R)) := by
  let X := f.range
  let e : R ≃* X := MonoidHom.ofInjective hf
  have hYX : P.Y ≤ X := hA ▸ A.map_le_range f
  have hC : (Subgroup.center R).map f = (Subgroup.center X).map X.subtype := by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨e r, (Subgroup.centerCongr e ⟨r, hr⟩).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e.symm x, (Subgroup.centerCongr e.symm ⟨x, hx⟩).property, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply x)
  have hB : (A ⊔ Subgroup.center R).map f = P.Y ⊔ (Subgroup.center X).map X.subtype := by
    rw [Subgroup.map_sup, hA, hC]
  have hcard : Nat.card A = 2 ^ (n + 1) := by
    rw [← Subgroup.card_map_of_injective hf, hA]
    exact P.quaternion_subgroup.2.1
  obtain ⟨r, hr, hc, hproper | ⟨hfull, hrn, hi, a, ha, hout, hsq⟩⟩ :=
    P.overgroup_central_product_extension_data X hYX
  · refine ⟨hcard, r, hr, (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans hc, Or.inl ?_⟩
    apply Subgroup.map_injective hf
    rw [hB, ← hproper, ← MonoidHom.range_eq_map]
  · refine ⟨hcard, r, hr, (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans hc,
      Or.inr ⟨MonoidHom.range_eq_top.mp hfull, hrn, ?_, ?_⟩⟩
    · have he := Subgroup.relIndex_map_map_of_injective (A ⊔ Subgroup.center R) ⊤ hf
      rw [Subgroup.relIndex_top_right] at he
      rw [hB, ← MonoidHom.range_eq_map] at he
      exact he.symm.trans hi
    · obtain ⟨b, hb⟩ := ha
      refine ⟨b, ?_, ?_⟩
      · intro h
        apply hout
        rw [← hB, ← hb]
        exact Subgroup.mem_map_of_mem f h
      · apply Subgroup.map_injective hf
        rw [MonoidHom.map_zpowers, map_pow, hb, hC]
        exact hsq

end ABG.Wreathed.Presentation

