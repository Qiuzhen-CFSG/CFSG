module

public import CFSG.Quasithin.ClassificationModels
public import CFSG.Quasithin.Models

/-!
# Inclusion of the earlier partial output API

Every witness in `IsConstructedQTKEModel` supplies the same concrete model
witness in `IsQTKEModelWithoutReeF4`, hence in the complete `IsQTKEModel` list. The proof
separates the rank-one, rank-two and binary higher-rank cases by their exact
parameters. No comparison isomorphism or recognition theorem is needed.

Source: the Main Theorem on pp.4 and 482 of Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript.
This compatibility extension imports the old API; the main definitions do not.
-/

public section

namespace CFSG.Quasithin

open ClassificationModels

variable {G : Type*} [Group G]

theorem IsMathieuModel.toClassificationSporadic (h : IsMathieuModel G) :
    IsSporadicModel G := by
  rcases h with h | h | h | h | h
  · exact ⟨.m11, h⟩
  · exact ⟨.m12, h⟩
  · exact ⟨.m22, h⟩
  · exact ⟨.m23, h⟩
  · exact ⟨.m24, h⟩

theorem IsConstructedQTKEModel.toQTKEModelWithoutReeF4 (h : IsConstructedQTKEModel G) :
    IsQTKEModelWithoutReeF4 G := by
  cases h with
  | alternating n hn iso => exact .alternating n hn iso
  | linear_even n f hp iso =>
      rcases hp with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨hn, rfl⟩
      · exact .bender (.linear f hf iso)
      · exact .rank_two f (.linear hf iso)
      · exact .linear_binary n hn iso
  | unitary_even n f hp iso =>
      rcases hp with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, rfl⟩
      · exact .bender (.unitary f hf iso)
      · exact .rank_two f (.unitary_four hf iso)
      · exact .rank_two 2 (.unitary_five rfl iso)
  | symplectic_even r f hp iso =>
      rcases hp with ⟨rfl, hf⟩ | ⟨rfl, rfl⟩
      · exact .rank_two f (.symplectic hf iso)
      · exact .symplectic_binary iso
  | linear_prime p hp hlarge iso => exact .linear_prime p hp hlarge iso
  | linear_three n hn iso => exact .linear_three n hn iso
  | unitary_three n hn iso => exact .unitary_three n hn iso
  | suzuki m hm iso => exact .bender (.suzuki m hm iso)
  | mathieu h => exact .sporadic h.toClassificationSporadic
  | tits iso => exact .rank_two 1 (.tits rfl iso)

/-- The earlier constructed API embeds in the complete Main Theorem output. -/
theorem IsConstructedQTKEModel.toQTKEModel (h : IsConstructedQTKEModel G) :
    ClassificationModels.IsQTKEModel G := h.toQTKEModelWithoutReeF4.toQTKEModel

end CFSG.Quasithin
