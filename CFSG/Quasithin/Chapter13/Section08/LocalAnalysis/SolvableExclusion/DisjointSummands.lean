module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.FixedSpace

/-!
# The disjoint-summand step in the five-primary case

The fixed-space calculation traps [U₂,Vγ] in A₁. If the image of A₁ lies
in Ũ₁, while Vγ normalizes U₂, then the image of [U₂,B₂] lies in both
Ũ₁ and Ũ₂. Their disjointness forces this image to be trivial.
The quotient is literally U_H/V₁ and all images use its quotient map.
This is the last inference of Aschbacher–Smith 13.8.13, printed p.951
(combined manuscript of 1 March 2004). The model analysis must still produce
the two factors and prove that B₂ acts nontrivially on the second one.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
open Subgroup
variable {G : Type*} [Group G]

/-- The image of a subgroup in the actual quotient U_H/V₁. Uses with an
intrinsic subgroup carrier must establish X ≤ U_H. -/
def tildeImage (UH V₁ X : Subgroup G) [(V₁.subgroupOf UH).Normal] :
    Subgroup (UH ⧸ V₁.subgroupOf UH) :=
  (X.subgroupOf UH).map (QuotientGroup.mk' (V₁.subgroupOf UH))

/-- The terminal conclusion is an actual vanishing commutator image, not
an assumed impossible witness. It contradicts the nontrivial B₂ action
only after that action is established by the five-primary calculation. -/
theorem second_summand_commutator_image_eq_bot
    (UH Uγ Vγ A₁ V₁ U₁ U₂ B₂ : Subgroup G) [(V₁.subgroupOf UH).Normal]
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = 2)
    (hnA : UH ≤ normalizer (A₁ : Set G))
    (hnV : UH ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅UH, Uγ⁆ ≤ A₁ ⊔ V₁)
    (hdis : Disjoint V₁ A₁) (hU₂ : U₂ ≤ UH) (hfixed : ⁅U₂, Uγ⁆ ≤ V₁)
    (h13737 : ⁅UH ⊓ centralizer (Uγ : Set G), Vγ⁆ ≤ A₁)
    (hB₂ : B₂ ≤ Vγ) (hn₂ : Vγ ≤ normalizer (U₂ : Set G))
    (hline : tildeImage UH V₁ A₁ ≤ tildeImage UH V₁ U₁)
    (hsum : Disjoint (tildeImage UH V₁ U₁) (tildeImage UH V₁ U₂)) :
    tildeImage UH V₁ ⁅U₂, B₂⁆ = ⊥ := by
  have hcomm := (second_factor_commutator_le_line UH Uγ Vγ A₁ V₁ U₂
    hindex hnA hnV hmoved hdis hU₂ hfixed h13737).2
  have hcA : ⁅U₂, B₂⁆ ≤ A₁ := (commutator_mono le_rfl hB₂).trans hcomm
  have hc₂ : ⁅U₂, B₂⁆ ≤ U₂ :=
    le_normalizer_iff_commutator_le_left.mp (hB₂.trans hn₂)
  have hiA : tildeImage UH V₁ ⁅U₂, B₂⁆ ≤ tildeImage UH V₁ A₁ :=
    map_mono (fun _ hx => hcA hx)
  have hi₂ : tildeImage UH V₁ ⁅U₂, B₂⁆ ≤ tildeImage UH V₁ U₂ :=
    map_mono (fun _ hx => hc₂ hx)
  apply le_bot_iff.mp
  rw [← disjoint_iff.mp hsum]
  exact le_inf (hiA.trans hline) hi₂

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
end
