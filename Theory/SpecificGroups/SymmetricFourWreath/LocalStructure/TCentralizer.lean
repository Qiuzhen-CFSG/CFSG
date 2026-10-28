module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Planes

/-!
# The marked involution centralizer inside the original model Sylow

An element of the dihedral wreath product centralizing the first-factor
central involution cannot swap the factors. Hence its centralizer in the
marked Sylow is exactly the dihedral base, of index two.

Source: Aschbacher–Smith 13.9.2(6), printed p.969 (PDF p.986).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private instance : DecidableEq W := (RegularWreathProduct.equivProd S4 C2).injective.decidableEq
private theorem centralizer_t_coordinate : ∀a:P,
    sylowEmbedding a*t=t*sylowEmbedding a → a.right=1 := by decide +kernel

theorem centralizer_t_in_standardSylow :
    (standardSylow:Subgroup W)⊓centralizer ({t}:Set W)=J := by
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    obtain ⟨a,ha⟩ := hx
    apply (mem_J x).mpr
    refine ⟨?_,(mem_standardSylow x).mp ⟨a,ha⟩⟩
    rw [←ha] at hc ⊢
    exact centralizer_t_coordinate a (mem_centralizer_singleton_iff.mp hc)
  · exact le_inf (map_le_range _ _) J_le_centralizer_t
end SymmetricFourWreath
