module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Cyclic kernels of the literal D.2.17 endpoint

A marked source involution moves its prime core because its full kernel
commutator is nontrivial. If that prime core is cyclic, so is the original
kernel. The order-nine and extraspecial endpoint kernels are then excluded
by their exponents, leaving precisely the cyclic-three and cyclic-five
marked endpoints.

Source: Aschbacher--Smith D.2.17(1)--(4), used in 15.1.2, printed p.1086.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

omit [Finite G] in
theorem LocalGeneration.involution_not_centralizer_core (l : LocalGeneration ρ) :
    l.involution ∉ centralizer (pCore l.prime G : Set G) := by
  let := l.normal
  have hle : l.kernel ≤ pCore l.prime G := le_sSup ⟨l.normal,l.pgroup⟩
  intro hc
  have hh : zpowers l.involution ≤ centralizer (l.kernel : Set G) := by
    rw [zpowers_le]
    exact fun x hx => hc x (hle hx)
  have hz : ⁅l.kernel,zpowers l.involution⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh)
  exact l.nontrivial (l.commutator.symm.trans hz)

omit [Finite G] in
theorem LocalGeneration.kernel_isCyclic_of_core (l : LocalGeneration ρ)
    (hc : IsCyclic (pCore l.prime G)) : IsCyclic l.kernel := by
  let := l.normal
  let := hc
  have hle : l.kernel ≤ pCore l.prime G := le_sSup ⟨l.normal,l.pgroup⟩
  exact isCyclic_of_injective (inclusion hle) (inclusion_injective hle)

universe u
variable {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) D W}

theorem LocalGeneration.cyclic_endpoints (l : LocalGeneration σ)
    (hf : Function.Injective σ) (hc : IsCyclic l.kernel) :
    letI := BinaryGroupAction.action σ
    letI : Finite W := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
    letI := l.normal
    Section02.CyclicThreeEndpoint (V := Multiplicative W) l.kernel l.involution ∨
      Section02.CyclicFiveEndpoint (V := Multiplicative W) l.kernel l.involution := by
  let := BinaryGroupAction.action σ
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let := l.normal
  let := hc
  rcases l.endpoints hf with h3 | h5 | h9 | h27
  · exact Or.inl h3
  · exact Or.inr h5
  · let := h9.kernel_elementary
    have hh := IsElementaryAbelian.exponent_dvd_p 3 l.kernel
    rw [IsCyclic.exponent_eq_card,h9.card_kernel] at hh
    norm_num at hh
  · have hh := IsCyclic.exponent_eq_card (α := l.kernel)
    rw [h27.exponent_kernel,h27.card_kernel] at hh
    norm_num at hh
end CFSG.Quasithin.ChapterD.CyclicSource
