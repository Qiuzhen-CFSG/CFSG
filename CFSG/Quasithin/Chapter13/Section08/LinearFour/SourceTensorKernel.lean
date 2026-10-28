module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorSeed
public import Theory.Representation.CyclicSeedTensor.Kernel
public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# The maximal quotient's kernel on the first tensor

Let N be an L-invariant proper subgroup of U_L containing V. Irreducibility
of the actual section U_H/V₃ and generation U_L = ⟨U_H^L⟩ give
U_H ∩ N = V₃. The marked shear from L then extracts the second tensor
coordinate and proves U₀ ∩ N = V. Thus the images of U_H and U₀ in the
literal quotient U_L/N have orders four and sixteen.

The seed actor J may be U_H L₀; no containment of U_H in L₀ is imposed.
Normality of N is relative to L. Both the original coordinate homomorphism
and the specified shear are retained. The initial tensor/seed markings and
the later orthogonal and second-tensor geometry remain source obligations
of qt-d-138-linear-four-source. This does not complete 13.8.30 or 13.8.28.

Source: Aschbacher–Smith, 13.8.29(3)–13.8.30, printed p.964.
-/

public section
open scoped TensorProduct
open Subgroup Representation
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U W X : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]
  (UH V2 : Subgroup G) (π : G2 V2 →* K × I)
  (ρ : Representation (ZMod 2) (K × I) W)
  (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
  (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
  (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
  (himage : f.range.toSubmodule = d.imageSpace UH)
  (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
  (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
  (ht : t first = f u₀) (a : I) (ha : μ a first = second)
  (hf : Function.Injective f) (b : I)
  (hb0 : μ b first = first) (hb1 : μ b second = first + second)

include himage hcyclic ht ha hf hb0 hb1 in
theorem source_tensor_kernel (V N : Subgroup G)
    (hV2V : V2 ≤ V) (hVS : V ≤ U0 UH V2) (hVN : V ≤ N)
    (hfirstmeet : UH ⊓ N ≤ V)
    (htimage : t.range.toSubmodule = d.imageSpace V)
    (β : G2 V2) (hβ : π β = (1,b)) (hβN : (β : G) ∈ normalizer N) :
    U0 UH V2 ⊓ N = V := by
  have honto : Function.Surjective (coordinateMap ρ σ f a) := by
    intro w
    obtain ⟨z,hz⟩ := source_tensor_map_surjective UH V2 π ρ σ μ d f himage
      u₀ hcyclic t ht a ha w
    exact ⟨TensorProduct.piScalarRight (ZMod 2) (ZMod 2) U (Fin 2) z,hz⟩
  have he : d.imageSpace N = t.range.toSubmodule := by
    apply kernel_eq_seed_of_shear ρ σ μ f a u₀ hcyclic t ht ha b hb0 hb1 honto
    · rw [htimage]
      exact d.imageSpace_mono hVN
    · intro u hu
      have hfu : f u ∈ d.imageSpace UH := by rw [← himage]; exact ⟨u,rfl⟩
      obtain ⟨x,hx,hfx⟩ := (d.mem_imageSpace_iff UH _).mp hfu
      have hxN : (x : G) ∈ N :=
        (d.coordinates_mem_imageSpace_iff_of_kernel_le N (hV2V.trans hVN) x).mp (hfx.symm ▸ hu)
      have hv : f u ∈ t.range.toSubmodule := by
        rw [htimage]
        exact (d.mem_imageSpace_iff V _).mpr ⟨x,hfirstmeet ⟨hx,hxN⟩,hfx⟩
      exact first_mem_seed ρ σ μ f a u₀ hcyclic t ht ha hf b hb0 hb1 u hv
    · intro w hw
      obtain ⟨x,hx,rfl⟩ := (d.mem_imageSpace_iff N _).mp hw
      refine (d.mem_imageSpace_iff N _).mpr ⟨⟨β * x * (β : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized β.property) x).mp x.property⟩,
        (mem_normalizer_iff.mp hβN x).mp hx, ?_⟩
      have hh := d.equivariant β x
      change (d.coordinates _).toAdd = ρ (π β) _ at hh
      rwa [hβ] at hh
  apply le_antisymm ?_ (le_inf hVS hVN)
  intro x hx
  apply (d.coordinates_mem_imageSpace_iff_of_kernel_le V hV2V ⟨x,hx.1⟩).mp
  rw [← htimage, ← he]
  exact (d.mem_imageSpace_iff N _).mpr ⟨⟨x,hx.1⟩,hx.2,rfl⟩

theorem source_maximal_kernel_on_first (L J UL N V3 : Subgroup G)
    (hUL : UL = conjugateSpanBy UH L) (hN : L ≤ normalizer N)
    (hproper : ¬ UL ≤ N) (hJL : J ≤ L)
    (ψ : Representation (ZMod 2) J X) [IsIrreducible ψ]
    (s : BinaryConjugationSection J UH V3 ψ) (hV3N : V3 ≤ N) : UH ⊓ N = V3 := by
  apply s.inf_eq_kernel_of_irreducible N (hJL.trans hN) hV3N
  intro hUN
  apply hproper
  rw [hUL]
  exact conjugateSpanBy_le hUN hN
end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Subgroup Representation
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U W X : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]
  (UH V2 : Subgroup G) (π : G2 V2 →* K × I)
  (ρ : Representation (ZMod 2) (K × I) W)
  (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
  (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
  (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
  (himage : f.range.toSubmodule = d.imageSpace UH)
  (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
  (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
  (ht : t first = f u₀) (a : I) (ha : μ a first = second)
  (hf : Function.Injective f) (b : I)
  (hb0 : μ b first = first) (hb1 : μ b second = first + second)


include himage hcyclic ht ha hf hb0 hb1 in
theorem source_maximal_tensor_kernels (L J UL N V3 V : Subgroup G)
    (hUL : UL = conjugateSpanBy UH L) (hN : L ≤ normalizer N)
    (hproper : ¬ UL ≤ N) (hJL : J ≤ L)
    (ψ : Representation (ZMod 2) J X) [IsIrreducible ψ]
    (s : BinaryConjugationSection J UH V3 ψ) (hV3V : V3 ≤ V)
    (hV2V : V2 ≤ V) (hVS : V ≤ U0 UH V2) (hVN : V ≤ N)
    (htimage : t.range.toSubmodule = d.imageSpace V)
    (β : G2 V2) (hβ : π β = (1,b)) (hβL : (β : G) ∈ L) :
    UH ⊓ N = V3 ∧ U0 UH V2 ⊓ N = V := by
  have hfirst := source_maximal_kernel_on_first UH L J UL N V3
    hUL hN hproper hJL ψ s (hV3V.trans hVN)
  refine ⟨hfirst, source_tensor_kernel UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 V N hV2V hVS hVN ?_ htimage β hβ (hN hβL)⟩
  rw [hfirst]
  exact hV3V

include himage hcyclic ht ha hf hb0 hb1 in
theorem source_maximal_tensor_image_orders [Finite G] [FiniteDimensional (ZMod 2) U]
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    (hd : Module.finrank (ZMod 2) U = 3) (hu₀ : u₀ ≠ 0)
    (L J UL N V3 V : Subgroup G)
    (hUL : UL = conjugateSpanBy UH L) (hN : L ≤ normalizer N)
    (hproper : ¬ UL ≤ N) (hJL : J ≤ L)
    (ψ : Representation (ZMod 2) J X) [IsIrreducible ψ]
    (s : BinaryConjugationSection J UH V3 ψ) (hseedDim : Module.finrank (ZMod 2) X = 2)
    (hV3V : V3 ≤ V) (hV2V : V2 ≤ V) (hVS : V ≤ U0 UH V2) (hVN : V ≤ N)
    (htimage : t.range.toSubmodule = d.imageSpace V)
    (β : G2 V2) (hβ : π β = (1,b)) (hβL : (β : G) ∈ L)
    (η : Representation (ZMod 2) L Z) (q : BinaryConjugationSection L UL N η)
    (hSU : U0 UH V2 ≤ UL) :
    Nat.card (q.imageSpace UH) = 4 ∧ Nat.card (q.imageSpace (U0 UH V2)) = 16 := by
  obtain ⟨hfirst,hkernel⟩ := source_maximal_tensor_kernels UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 L J UL N V3 V hUL hN hproper hJL
    ψ s hV3V hV2V hVS hVN htimage β hβ hβL
  have hfirstcard : V3.relIndex UH = 4 := by
    let : Finite X := Finite.of_surjective (fun x : UH => (s.coordinates x).toAdd)
      (Multiplicative.toAdd.surjective.comp s.onto)
    let := s.kernel_normal
    calc
      V3.relIndex UH = Nat.card X := Nat.card_congr s.quotientEquiv.toEquiv
      _ = 4 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hseedDim]
        decide
  have hsecondcard := source_tensor_seed_index UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ V hV2V hVS htimage
  constructor
  · rw [q.imageSpace_card_eq_relIndex UH ((UH_le_U0 UH V2).trans hSU),
      ← inf_relIndex_right N UH, inf_comm, hfirst]
    exact hfirstcard
  · rw [q.imageSpace_card_eq_relIndex (U0 UH V2) hSU,
      ← inf_relIndex_right N (U0 UH V2), inf_comm, hkernel]
    exact hsecondcard
end CFSG.Quasithin.Chapter13.Section08.LinearFour

