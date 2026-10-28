module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.ProductAssembly

/-!
# The binary linear-three catalogue from the concrete flag maps

A two-group flag stabilizer supplies a nonzero map from the flag permutation
module onto any irreducible binary module. The given equivariant flag
decomposition and the two natural-dual core exact sequences then force the
quotient to be the trivial, natural, dual-natural, or adjoint module.

This proves the assembly implication for Aschbacher–Smith H.6.1 from the
actual H.5.3 and H.6.2 maps, printed pp.385–387. The finite flag construction
must supply those maps; an irreducible catalogue is never an input. The
three model irreducibility statements are proved by matrix density.
-/

public section

open Representation
namespace BinaryLinearThree.IrreducibleCatalogue

set_option backward.isDefEq.respectTransparency false in
theorem classify_from_flag_decomposition
    {Ω C : Type*} [Fintype Ω] [AddCommGroup C] [Module (ZMod 2) C]
    (τ : Group →* Equiv.Perm Ω) (o : Ω)
    (H : Subgroup Group) (hH : IsPGroup 2 H)
    (hstab : ∀ g : Group, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : Group, τ g o = x)
    (σ : Representation (ZMod 2) Group C)
    (pointIn : W.dual.IntertwiningMap U₂) (pointOut : U₂.IntertwiningMap W)
    (pointSurj : Function.Surjective pointOut)
    (pointExact : LinearMap.range pointIn.toLinearMap = LinearMap.ker pointOut.toLinearMap)
    (lineIn : W.IntertwiningMap σ) (lineOut : σ.IntertwiningMap W.dual)
    (lineSurj : Function.Surjective lineOut)
    (lineExact : LinearMap.range lineIn.toLinearMap = LinearMap.ker lineOut.toLinearMap)
    (e : Representation.Equiv ((BinaryPermutation.representation Ω).comp τ)
      ((Representation.trivial (ZMod 2) Group (ZMod 2)).prod (U₂.prod (σ.prod S))))
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) Group M) [IsIrreducible ρ] :
    Nonempty (ρ.Equiv (Representation.trivial (ZMod 2) Group (ZMod 2))) ∨
      Nonempty (ρ.Equiv W) ∨ Nonempty (ρ.Equiv W.dual) ∨ Nonempty (ρ.Equiv S) := by
  let : IsIrreducible W := natural_irreducible
  let : IsIrreducible W.dual := dual_irreducible
  let : IsIrreducible S := steinberg_irreducible
  let : Nontrivial M := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨f,hf⟩ := irreducible_permutation_quotient τ o H hH hstab htrans ρ
  let q := f.comp e.symm.toIntertwiningMap
  have hq : q ≠ 0 := by
    intro hz
    obtain ⟨m,hm⟩ := exists_ne (0 : M)
    obtain ⟨x,hx⟩ := hf m
    have he := congrArg (fun h => h (e x)) hz
    have he' : f x = 0 := by simpa [q] using he
    exact hm (hx.symm.trans he')
  exact classify_product_extension_quotient pointIn pointOut pointSurj pointExact
    lineIn lineOut lineSurj lineExact q hq

end BinaryLinearThree.IrreducibleCatalogue
