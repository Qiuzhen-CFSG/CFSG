module

public import Theory.Representation.BinaryOffender.OddNormalFixedSpace
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic

/-!
# The two fixed-space reductions in B.1.10

For H = NKA with N normal and odd, the two-core Q of H lies in KA,
centralizes NK, and is exactly the kernel on C_V(Q). All groups and the
representation are restricted to H before taking the core or fixed space.
The Fitting specialization discharges oddness from O₂(G) = 1. Keeping N
arbitrary also supplies the later reduction with N = C_F(G)(J*).

Source: Aschbacher–Smith, B.1.10, printed p.72 (PDF p.83).
-/

public section
namespace CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
open Subgroup Theory.GroupTheory Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The fixed-space kernel calculation inside the actual generated overgroup. -/
theorem normalOdd_fixedSpace_kernel (hfaith : Function.Injective ρ)
    (N K A : Subgroup G) [N.Normal] (hN : Nat.Coprime 2 (Nat.card N))
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K,A⁆) :
    let H := N ⊔ (K ⊔ A)
    let τ := ρ.comp H.subtype
    let Q := pCore 2 H
    Q ≤ (K ⊔ A).subgroupOf H ∧
    Q ≤ centralizer ((N ⊔ K).subgroupOf H : Set H) ∧
    subspaceKernel τ (fixedSpace τ Q) ⊤ = Q := by
  let H := N ⊔ (K ⊔ A)
  let N₀ := N.subgroupOf H
  let K₀ := K.subgroupOf H
  let A₀ := A.subgroupOf H
  have hNH : N ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_left.trans le_sup_right
  have hAH : A ≤ H := le_sup_right.trans le_sup_right
  have hN₀ : Nat.Coprime 2 (Nat.card N₀) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]
  have hK₀ : IsQuasisimple K₀ ∨ Nat.Coprime 2 (Nat.card K₀) := by
    rcases hK with hK | hK
    · let : IsQuasisimple K := hK
      exact Or.inl (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKH).symm)
    · right
      rw [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv, hK]
      decide
  have hA₀ : IsPGroup 2 A₀ := by
    let : IsElementaryAbelian 2 A := hA.1.2
    exact (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  have hcomm : ⁅K₀,A₀⁆ = K₀ := by
    apply Subgroup.map_injective H.subtype_injective
    simp only [K₀, A₀, map_commutator, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le hAH, ← hKA]
  have hgen : N₀ ⊔ (K₀ ⊔ A₀) = ⊤ := by
    rw [← subgroupOf_sup hKH hAH, ← subgroupOf_sup hNH le_sup_right]
    exact subgroupOf_self H
  obtain ⟨hQKA, hQNK⟩ := twoCore_le_and_centralizes_of_odd_normal_supplement
    N₀ K₀ A₀ hN₀ hK₀ hcomm hgen
  refine ⟨?_, ?_, fixedSpace_kernel_eq_twoCore_of_odd_normal_supplement
    (ρ.comp H.subtype) (hfaith.comp H.subtype_injective) N₀ K₀ A₀ hN₀ hK₀ hA₀ hcomm hgen⟩
  · rwa [subgroupOf_sup hKH hAH]
  · rwa [subgroupOf_sup hNH hKH]

/-- The first source reduction, with oddness of F(G) proved from its prime cores. -/
theorem fitting_fixedSpace_kernel (hfaith : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K,A⁆) :
    let H := fittingSubgroup G ⊔ (K ⊔ A)
    let τ := ρ.comp H.subtype
    let Q := pCore 2 H
    Q ≤ (K ⊔ A).subgroupOf H ∧
    Q ≤ centralizer ((fittingSubgroup G ⊔ K).subgroupOf H : Set H) ∧
    subspaceKernel τ (fixedSpace τ Q) ⊤ = Q := by
  apply normalOdd_fixedSpace_kernel ρ hfaith (fittingSubgroup G) K A _ hK hA hKA
  exact (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
    (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))

end CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
