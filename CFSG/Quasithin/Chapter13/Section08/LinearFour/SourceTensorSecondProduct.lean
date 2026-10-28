module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.Constructions
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.Representation.CyclicSeedTensor.ThreeSlices

/-!
# The three-conjugate product in the second tensor

The marked slices in either second-tensor row span the quotient V₀/U₀.
Lift their three coordinates to elements of V_H, V_H^g and V_H^(g²),
then absorb the remaining kernel element into V_H. This proves the ordered
product in source 13.8.29(4) without assuming V₀ itself elementary abelian.
The same source g is retained, with inverse conjugation and the original
quotient map. The initial tensor markings remain with
qt-d-138-linear-four-source; earlier 13.8.27 belongs to
qt-d-138-six-g2-source and final assembly to qt-d-1381-source.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), 13.8.29(4), printed p.964.
-/

public section
open scoped TensorProduct


open Subgroup Representation
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I T Y E : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup T] [Module (ZMod 2) T] [AddCommGroup Y] [Module (ZMod 2) Y]
  [AddCommGroup E] [Module (ZMod 2) E]

/-- Spanning by three tensor slices lifts to the ordered product of the three
actual conjugates, absorbing the literal kernel in the first factor. -/
theorem source_second_tensor_three_product
    (UH V2 VH : Subgroup G) (hUV : U0 UH V2 ≤ VH)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K T)
    (μ : Representation (ZMod 2) I E) (ρ : Representation (ZMod 2) (K × I) Y)
    (p : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ρ.comp π))
    (e : (externalTensor σ μ).Equiv ρ) (v : E) (c : I)
    (hspan : ∀ z : E, ∃ r s t : ZMod 2,
      z = r • v + s • μ c v + t • μ c (μ c v))
    (hslice : ∀ u, e (u ⊗ₜ[ZMod 2] v) ∈ p.imageSpace VH)
    (g : G2 V2) (hg : π g⁻¹ = (1,c)) (x : G) (hx : x ∈ V0 VH V2) :
    ∃ u ∈ VH, ∃ v ∈ VH, ∃ w ∈ VH,
      x = u * ((g : G)⁻¹ * v * (g : G)) * ((g : G)⁻¹ ^ 2 * w * (g : G) ^ 2) := by
  let xA : V0 VH V2 := ⟨x,hx⟩
  obtain ⟨z,hz⟩ := e.surjective (p.coordinates xA).toAdd
  obtain ⟨u₀,u₁,u₂,he⟩ := tensor_three_slices v (μ c v) (μ c (μ c v)) hspan z
  have hequiv (u : T) (v' : E) :
      ρ (1,c) (e (u ⊗ₜ[ZMod 2] v')) = e (u ⊗ₜ[ZMod 2] μ c v') := by
    have hh := IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (1,c) (u ⊗ₜ[ZMod 2] v')
    simpa [externalTensor_apply, TensorProduct.map_tmul] using hh.symm
  have hcoord : e (u₀ ⊗ₜ[ZMod 2] v) + ρ (1,c) (e (u₁ ⊗ₜ[ZMod 2] v)) +
      ρ (1,c) (ρ (1,c) (e (u₂ ⊗ₜ[ZMod 2] v))) = (p.coordinates xA).toAdd := by
    simp only [hequiv]
    rw [← map_add, ← map_add, ← he]
    exact hz
  obtain ⟨y₀,hy₀,he₀⟩ := (p.mem_imageSpace_iff VH _).mp (hslice u₀)
  obtain ⟨y₁,hy₁,he₁⟩ := (p.mem_imageSpace_iff VH _).mp (hslice u₁)
  obtain ⟨y₂,hy₂,he₂⟩ := (p.mem_imageSpace_iff VH _).mp (hslice u₂)
  let α := g⁻¹
  let conj (y : V0 VH V2) : V0 VH V2 :=
    ⟨(α : G) * y * (α : G)⁻¹,
      (mem_normalizer_iff.mp (p.normalized α.property) y).mp y.property⟩
  have hconj (y : V0 VH V2) : (p.coordinates (conj y)).toAdd =
      ρ (1,c) (p.coordinates y).toAdd := by
    have hh := p.equivariant α y
    change (p.coordinates (conj y)).toAdd = ρ (π g⁻¹) (p.coordinates y).toAdd at hh
    rwa [hg] at hh
  let m := y₀ * conj y₁ * conj (conj y₂)
  have hm : p.coordinates m = p.coordinates xA := by
    apply Multiplicative.toAdd.injective
    simp only [m, map_mul, toAdd_mul, hconj]
    rw [he₀,he₁,he₂]
    exact hcoord
  have hk : ((xA * m⁻¹ : V0 VH V2) : G) ∈ U0 UH V2 := by
    apply (p.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, hm, mul_inv_cancel]
  refine ⟨(xA * m⁻¹ : V0 VH V2) * y₀, VH.mul_mem (hUV hk) hy₀,
    y₁,hy₁,y₂,hy₂, ?_⟩
  dsimp [xA, m, conj, α]
  simp only [inv_inv]
  group


/-- The natural second-tensor row gives the three-conjugate product with the
same inverse conjugation convention as the source. -/
theorem source_natural_second_tensor_product
    (UH V2 VH : Subgroup G) (hUV : U0 UH V2 ≤ VH)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K T)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (ρ : Representation (ZMod 2) (K × I) Y)
    (p : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ρ.comp π))
    (e : (externalTensor σ μ).Equiv ρ) (c : I)
    (hc0 : μ c first = second)
    (hslice : ∀ u, e (u ⊗ₜ[ZMod 2] first) ∈ p.imageSpace VH)
    (g : G2 V2) (hg : π g⁻¹ = (1,c)) (x : G) (hx : x ∈ V0 VH V2) :
    ∃ u ∈ VH, ∃ v ∈ VH, ∃ w ∈ VH,
      x = u * ((g : G)⁻¹ * v * (g : G)) * ((g : G)⁻¹ ^ 2 * w * (g : G) ^ 2) := by
  apply source_second_tensor_three_product UH V2 VH hUV π σ μ ρ p e first c
    ?_ hslice g hg x hx
  intro z
  refine ⟨z 0,z 1,0,?_⟩
  rw [hc0,zero_smul,add_zero]
  ext i
  fin_cases i <;> simp [first,second]

/-- All three cyclic translates are retained in the extra-line tensor row;
the resulting product uses the actual source g, g² and literal kernel U₀. -/
theorem source_extra_line_second_tensor_product
    (UH V2 VH : Subgroup G) (hUV : U0 UH V2 ≤ VH)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K T)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (ρ : Representation (ZMod 2) (K × I) Y)
    (p : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ρ.comp π))
    (e : (externalTensor σ (μ.prod (Representation.trivial (ZMod 2) I (ZMod 2)))).Equiv ρ)
    (c : I) (hc0 : μ c first = second) (hc1 : μ c second = first + second)
    (hslice : ∀ u, e (u ⊗ₜ[ZMod 2] (first, 1)) ∈ p.imageSpace VH)
    (g : G2 V2) (hg : π g⁻¹ = (1,c)) (x : G) (hx : x ∈ V0 VH V2) :
    ∃ u ∈ VH, ∃ v ∈ VH, ∃ w ∈ VH,
      x = u * ((g : G)⁻¹ * v * (g : G)) * ((g : G)⁻¹ ^ 2 * w * (g : G) ^ 2) := by
  apply source_second_tensor_three_product UH V2 VH hUV π σ
    (μ.prod (Representation.trivial (ZMod 2) I (ZMod 2))) ρ p e (first,(1 : ZMod 2)) c
    ?_ hslice g hg x hx
  intro z
  change ∃ r s t : ZMod 2, z = r • (first,(1 : ZMod 2)) + s • (μ c first,(1 : ZMod 2)) +
    t • (μ c (μ c first),(1 : ZMod 2))
  rw [hc0,hc1]
  exact natural_trivial_three_vectors z

end CFSG.Quasithin.Chapter13.Section08.LinearFour
