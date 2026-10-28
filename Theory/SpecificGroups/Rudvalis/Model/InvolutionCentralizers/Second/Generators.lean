module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Generator0
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Generator1
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Generator2
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Generator3

/-!
# Short words in the literal centralizer

Untrusted finite witnesses for the literal ATLAS generator a and its two-point
centralizer stabilizer chain. Every equation used below is checked by Lean's
kernel. No centralizer order or product structure is assumed.
Source: RuG1-p4060B0, attributed in Model.PermutationData; GLS3 Table 5.3r.
Reproduction data and procedure are in Second/source/.
-/

set_option Elab.async false
namespace Rudvalis.InvolutionCentralizers.SecondCertificate
open OuterNormalizer OuterNormalizer.InvarianceCertificate OuterNormalizer.RigidityCertificate

public theorem word_centralizes {n : Nat} (f : Fin n → Model)
    (hf : ∀ i, f i ∈ Subgroup.centralizer ({a} : Set Model))
    (w : List (Fin n)) : (w.map f).prod ∈ Subgroup.centralizer ({a} : Set Model) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  exact hf i

@[expose] public def letters0 : Fin 8 → Model := ![g0,g1,g2,g3,g0⁻¹,g1⁻¹,g2⁻¹,g3⁻¹]

public theorem letters0_mem (i : Fin 8) : letters0 i ∈ Subgroup.centralizer ({a} : Set Model) := by
  fin_cases i
  · exact Subgroup.mem_centralizer_singleton_iff.mpr g0_commutes
  · exact Subgroup.mem_centralizer_singleton_iff.mpr g1_commutes
  · exact Subgroup.mem_centralizer_singleton_iff.mpr g2_commutes
  · exact Subgroup.mem_centralizer_singleton_iff.mpr g3_commutes
  · apply (Subgroup.centralizer _).inv_mem
    exact Subgroup.mem_centralizer_singleton_iff.mpr g0_commutes
  · apply (Subgroup.centralizer _).inv_mem
    exact Subgroup.mem_centralizer_singleton_iff.mpr g1_commutes
  · apply (Subgroup.centralizer _).inv_mem
    exact Subgroup.mem_centralizer_singleton_iff.mpr g2_commutes
  · apply (Subgroup.centralizer _).inv_mem
    exact Subgroup.mem_centralizer_singleton_iff.mpr g3_commutes
end Rudvalis.InvolutionCentralizers.SecondCertificate
