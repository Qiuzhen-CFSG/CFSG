module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Elementary
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.QuotientCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.FixedKernel

/-!
# Self-centralization of the native elementary subgroup

An ambient centralizer element lies in the literal octad pullback Q. Correcting
it by an element of F with the same quotient image leaves a kernel element
centralizing the four lifts. The checked common fixed kernel lies in F, so the
original element does too. This proves the full ambient equality C(F)=F.
Source: Kleidman--Wilson (1988), Proposition 2.2.2, printed p.490.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount Subgroup
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis

private theorem localF_commute (f : M) (hf : f ∈ localF) (g : M) (hg : g ∈ localF) :
    Commute f g := by
  let _ := localF_elementary
  exact congrArg (fun a : localF => (a : M)) (mul_comm (⟨f, hf⟩ : localF) ⟨g, hg⟩)

private theorem lift_mem_localF (i : Fin 4) : lift i ∈ localF := by
  simpa only [generators, Fin.append_right] using generator_mem_localF (Fin.natAdd 6 i)

/-- The full centralizer in the native J4 carrier is exactly the constructed F. -/
theorem centralizer_F : centralizer (F : Set Model) = F := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (centralizer_F_le_Q hz)
    change projection x ∈ A at hx
    rw [← localF_image] at hx
    obtain ⟨f, hf, hfx⟩ := Subgroup.mem_map.mp hx
    have hker : x * f⁻¹ ∈ localKernel matrixA_mul_self matrixB_pow_four := by
      rw [← MathieuHallActors.projection_ker, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hfx, mul_inv_cancel]
    have hxc (i : Fin 4) : Commute x (lift i) := by
      apply Subtype.ext
      exact ((mem_centralizer_iff.mp hz) (lift i)
        (Subgroup.mem_map.mpr ⟨lift i, lift_mem_localF i, rfl⟩)).symm
    have hk : x * f⁻¹ ∈ localF := kernel_mem_localF_of_commuting_lifts _ hker
      (fun i => (hxc i).mul_left (localF_commute f hf (lift i) (lift_mem_localF i)).inv_left)
    have hxf : x ∈ localF := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using localF.mul_mem hk hf
    exact Subgroup.mem_map.mpr ⟨x, hxf, rfl⟩
  · intro x hx y hy
    let _ := F_elementary
    exact congrArg (fun a : F => (a : Model)) (mul_comm (⟨y, hy⟩ : F) ⟨x, hx⟩)

end Janko4.LocalStructure.LinearFive
