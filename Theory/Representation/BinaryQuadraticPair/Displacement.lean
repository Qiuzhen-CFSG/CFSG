module

public import Theory.Representation.BinaryQuadraticPair
open InvertedCubicTensor BinaryPermutation
open scoped TensorProduct
/-!
# Displacement across two natural S₃ summands

On the concrete natural binary module the displacement of one transposition
projects any other translate of its moved line back to that line. The checked
three-coordinate identity passes through every equivariant natural tensor.
Consequently a subspace has its exact translated preimage under displacement.
The quotient and action are retained by the adjoining conjugation-section API.
Source: Aschbacher–Smith, 13.7.10(4), printed p.941.
-/

public section
namespace Representation.BinaryQuadraticPair
local instance : DecidableEq S₃ := inferInstance
local instance : Fintype S₃ := inferInstance
local instance : Fintype (Fin 3 → ZMod 2) := inferInstance
private theorem coordinate_projection_identity :
    ∀ t g:S₃,t*t=1→t≠1→g≠1→g≠t→∀v:Fin 3→ZMod 2,
      (∑i,v i)=0→∀i:Fin 3,
      (v (t⁻¹ (g⁻¹ (t⁻¹ i))) - v (g⁻¹ (t⁻¹ i))) -
        (v (t⁻¹ (g⁻¹ i)) - v (g⁻¹ i)) = v (t⁻¹ i) - v i := by
  decide +kernel
private theorem natural_projection_identity
    (t g:S₃) (ht:t*t=1) (ht1:t≠1) (hg1:g≠1) (hgt:g≠t)
    (v:BinaryPermutation.core (Fin 3)) :
      (coreRepresentation (Fin 3) t - 1)
        (coreRepresentation (Fin 3) g ((coreRepresentation (Fin 3) t - 1) v)) =
      (coreRepresentation (Fin 3) t - 1) v := by
  apply Subtype.ext
  funext i
  exact coordinate_projection_identity t g ht ht1 hg1 hgt v.val
    ((BinaryPermutation.mem_core (Fin 3) v.val).mp v.property) i

variable {M V:Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Projection identity on every equivariantly marked natural tensor. -/
theorem displacement_projection_of_tensor
    (σ:Representation (ZMod 2) S₃ V)
    (e:M ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] V)
    (he:∀a z,e ((Representation.tprod (Representation.trivial (ZMod 2) S₃ M)
      (coreRepresentation (Fin 3))) a z)=σ a (e z))
    (t g:S₃) (ht:t*t=1) (ht1:t≠1) (hg1:g≠1) (hgt:g≠t) (v:V) :
    (σ t-1) (σ g ((σ t-1) v))=(σ t-1) v := by
  let τ:=Representation.tprod (Representation.trivial (ZMod 2) S₃ M) (coreRepresentation (Fin 3))
  have hdelta (a:S₃) (z:M ⊗[ZMod 2] BinaryPermutation.core (Fin 3)) :
      e ((τ a-1) z)=(σ a-1) (e z) := by
    change e (τ a z-z)=σ a (e z)-e z
    rw [map_sub,he]
  have hd (a:S₃) (m:M) (n:BinaryPermutation.core (Fin 3)) :
      (τ a-1) (m⊗ₜ[ZMod 2]n)=m⊗ₜ[ZMod 2]((coreRepresentation (Fin 3) a-1) n) := by
    change τ a (m⊗ₜ[ZMod 2]n)-m⊗ₜ[ZMod 2]n=_
    simp only [τ,Representation.tprod_apply,TensorProduct.map_tmul,Representation.trivial_apply,
      Module.End.one_apply,LinearMap.sub_apply,TensorProduct.tmul_sub]
  have hτ (z:M ⊗[ZMod 2] BinaryPermutation.core (Fin 3)) :
      (τ t-1) (τ g ((τ t-1) z))=(τ t-1) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m n =>
      rw [hd]
      change (τ t-1) (m⊗ₜ[ZMod 2](coreRepresentation (Fin 3) g ((coreRepresentation (Fin 3) t-1) n)))=_
      rw [hd,natural_projection_identity t g ht ht1 hg1 hgt n]
    | add x y hx hy => simp only [map_add,hx,hy]
  obtain ⟨z,rfl⟩:=e.surjective v
  calc
    (σ t-1) (σ g ((σ t-1) (e z))) = e ((τ t-1) (τ g ((τ t-1) z))) := by
      rw [hdelta,he,hdelta]
    _ = e ((τ t-1) z) := congrArg e (hτ z)
    _ = (σ t-1) (e z) := hdelta t z
/-- The exact translated preimage of an arbitrary subspace in the moved space. -/
theorem translated_subspace_preimage_of_tensor
    (σ:Representation (ZMod 2) S₃ V)
    (e:M ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] V)
    (he:∀a z,e ((Representation.tprod (Representation.trivial (ZMod 2) S₃ M)
      (coreRepresentation (Fin 3))) a z)=σ a (e z))
    (t g:S₃) (ht:t*t=1) (ht1:t≠1) (hg1:g≠1) (hgt:g≠t)
    (W U:Submodule (ZMod 2) V) (hW:LinearMap.range (σ t-1)=W)
    (x:V) (hx:x∈W.map (σ g)) :
    (σ t-1) x∈U ↔ x∈U.map (σ g) := by
  obtain ⟨v,hv,rfl⟩:=hx
  have hv':v∈LinearMap.range (σ t-1):=hW.symm ▸ hv
  obtain ⟨z,hz⟩:=hv'
  have hd:(σ t-1) (σ g v)=v := by
    rw [←hz]
    exact displacement_projection_of_tensor σ e he t g ht ht1 hg1 hgt z
  rw [hd]
  constructor
  · intro hu
    exact ⟨v,hu,rfl⟩
  · rintro ⟨u,hu,heq⟩
    exact ((σ.apply_bijective g).injective heq) ▸ hu
end Representation.BinaryQuadraticPair
