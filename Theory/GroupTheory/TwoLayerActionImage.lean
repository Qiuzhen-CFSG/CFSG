module

public import Theory.GroupTheory.TwoLayerCentralizer

/-!
# Action images of a two-layer fixer

If D fixes a finite p-subgroup W and its displacement on Q lies in W,
then its image under any homomorphism killing C(Q) is a p-group.
The two-layer centralization theorem kills Oᵖ(D), so the image is an
image of the actual p-group quotient D/Oᵖ(D). No faithfulness, normality,
or elementary-abelian assumption on Q is needed.

Source application: the original H/E action kernel in the residual-fifteen
branch of Aschbacher--Smith 15.1.15. Its image on an original chief factor
is a two-group; an independently two-core-free chief actor kills that image.
-/

public section
namespace Subgroup
variable {G F : Type*} [Group G] [Finite G] [Group F]

/-- Every action quotient killing C(Q) sends a two-layer fixer to a p-group. -/
theorem isPGroup_image_of_two_layer {p : ℕ} (D Q W : Subgroup G)
    (hW : IsPGroup p W) (hc : D ≤ centralizer (W : Set G))
    (hd : ⁅D, Q⁆ ≤ W) (f : G →* F)
    (hf : centralizer (Q : Set G) ≤ f.ker) : IsPGroup p (D.map f) := by
  have hres : (pResidual p D).map D.subtype ≤ f.ker :=
    (residual_centralizes_of_two_layer D Q W hW hc hd).trans hf
  intro x
  obtain ⟨d, hdD, he⟩ := x.property
  obtain ⟨n, hn⟩ := isPGroup_quotient_pResidual (G := D) p
    (QuotientGroup.mk' (pResidual p D) ⟨d, hdD⟩)
  have hnD : (⟨d, hdD⟩ : D) ^ p ^ n ∈ pResidual p D :=
    (QuotientGroup.eq_one_iff _).mp hn
  refine ⟨n, Subtype.ext ?_⟩
  change (x : F) ^ p ^ n = 1
  rw [← he, ← map_pow]
  exact hres (mem_map_of_mem D.subtype hnD)

end Subgroup
