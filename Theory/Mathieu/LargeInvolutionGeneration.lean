module

public import Theory.Mathieu.LargeInvolutionGeneration.Certificates24
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage

/-!
# Bounded involution generation in the native large Mathieu groups

Three conjugates of every nonidentity involution generate M23; four generate
M24. The checked words recover generators of the full design automorphism
groups. Exhaustive Sylow fusion then transports these certificates to every
involution, keeping all conjugators in the respective native group.

Source: Guralnick--Malle, *Classification of 2F-modules I*, equations
(2.5)--(2.6) and Proposition 5.1, manuscript pp.4,16--17.
-/

public section
namespace Sporadic.Mathieu.LargeInvolutionGeneration
open Subgroup

/-- Three conjugates of the marked M23 involution generate the native carrier. -/
theorem representative23_generates :
    ∃ c : Fin 3 → M23, closure (Set.range fun i => c i * a23 * (c i)⁻¹) = ⊤ := by
  refine ⟨conjugator23, ?_⟩
  have hm (i : Fin 3) : target23 i ∈ closure (Set.range conjugate23) :=
    generation23 i ▸ evalWord_mem_closure conjugate23 (generationWord23 i)
  exact m23_eq_top_of_generators _ (hm 0) (hm 1) (hm 2)

/-- Four conjugates of either marked M24 involution generate the native carrier. -/
theorem representative24_generates (k : Fin 2) :
    ∃ c : Fin 4 → M24,
      closure (Set.range fun i => c i * representative24 k * (c i)⁻¹) = ⊤ := by
  refine ⟨conjugator24 k, ?_⟩
  have hm (i : Fin 4) : target24 i ∈ closure (Set.range (conjugate24 k)) :=
    generation24 k i ▸ evalWord_mem_closure (conjugate24 k) (generationWord24 k i)
  exact m24_eq_top_of_generators _ (hm 0) (hm 1) (hm 2) (hm 3)

/-- Every involution of the full W23 automorphism group has three generating conjugates. -/
theorem m23_three_conjugates_generate (t : M23) (ht : orderOf t = 2) :
    ∃ c : Fin 3 → M23, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  exact conjugate_generation_of_isConj (M23Geometry.involution_isConj_representative t ht)
    representative23_generates

/-- Every involution of the full W24 automorphism group has four generating conjugates. -/
theorem m24_four_conjugates_generate (t : M24) (ht : orderOf t = 2) :
    ∃ c : Fin 4 → M24, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  rcases M24InvolutionCentralizers.involution_classes t ht with h | h
  · exact conjugate_generation_of_isConj h.symm (representative24_generates 0)
  · exact conjugate_generation_of_isConj h.symm (representative24_generates 1)

end Sporadic.Mathieu.LargeInvolutionGeneration
