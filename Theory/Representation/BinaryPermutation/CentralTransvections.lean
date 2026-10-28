module

public import Theory.SpecificGroups.Symmetric.TranspositionSylow
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections
public import Theory.Representation.BinaryPermutation.FiveLowRank
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The S5 and S8 two-central transvection exclusions

On the actual natural S5 module, odd-degree transport identifies displacement
on the natural module with displacement on the permutation core. The checked
five-point calculation makes every nonidentity rank-one actor a transposition.
For S8 the stronger intrinsic theorem works in every faithful binary module.
The original full Sylow then contradicts the transposition centralizer order.

Source: Aschbacher–Smith G.6.4(4), printed p.346.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem five_isSwap_of_natural_rank_one
    (ρ : Representation (ZMod 2) G V) (e : G ≃* Equiv.Perm (Fin 5))
    (E : V ≃ₗ[ZMod 2] natural (Fin 5))
    (hE : ∀ g v, E (ρ g v) = naturalRepresentation (Fin 5) (e g) (E v))
    (a : G) (hne : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1) :
    (e a).IsSwap := by
  have he := fixedCodim_map_equivariant ρ (naturalRepresentation (Fin 5))
    e.toMonoidHom E hE (zpowers a)
  simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] at he
  have hc : Module.finrank (ZMod 2)
      (LinearMap.range (coreRepresentation (Fin 5) (e a) - LinearMap.id)) ≤ 1 := by
    rw [← fixedCodim_zpowers_eq_displacement_rank,
      fixedCodim_core_eq_full_odd (Fin 5) (by decide),
      ← fixedCodim_natural_eq_full_odd (Fin 5) (by decide), ← he,
      fixedCodim_zpowers_eq_displacement_rank]
    exact hr
  rcases FiveLowRank.low_rank (e a) hc with h | ⟨i,j,hij,hg⟩
  · exact (hne (e.injective (h.trans e.map_one.symm))).elim
  · exact ⟨i,j,hij,hg⟩

theorem not_twoCentral_natural_five
    (ρ : Representation (ZMod 2) G V) (e : G ≃* Equiv.Perm (Fin 5))
    (E : V ≃ₗ[ZMod 2] natural (Fin 5))
    (hE : ∀ g v, E (ρ g v) = naturalRepresentation (Fin 5) (e g) (E v))
    (a : G) (hne : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1)
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False :=
  Equiv.Perm.not_twoCentral_of_isSwap_model (Or.inl rfl) e a
    (five_isSwap_of_natural_rank_one ρ e E hE a hne hr) S hz

/-- The S8 exclusion needs no prior reconstruction of the actual module. -/
theorem not_twoCentral_faithful_eight
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (e : G ≃* Equiv.Perm (Fin 8)) (a : G) (hne : a ≠ 1) (ha : a ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  apply Equiv.Perm.not_twoCentral_of_isSwap_model (Or.inr rfl) e a ?_ S hz
  exact SymmetricEightTransvections.isSwap_of_fixedCodim_eq_one ρ hf e a hne ha
    (by rwa [fixedCodim_zpowers_eq_displacement_rank])
end BinaryPermutation
