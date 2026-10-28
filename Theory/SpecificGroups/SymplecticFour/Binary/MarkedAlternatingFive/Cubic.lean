module

public import Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.Embedding
public import Theory.Representation.SL2FourNaturalOrbits.CubicFixedSpace

/-!
# The cubic inside the marked natural alternating five

The diagonal field cubic belongs to the same literal embedded SL₂(4). It
normalizes the prescribed four-group, cycles its three nonidentity elements,
preserves its fixed plane, and has no nonzero fixed vector on the full module.
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
open Matrix Representation.SL2FourNatural
open Representation.SL2FourNatural.BorelFactors
open Representation.SL2FourNatural.PointCommutator
local notation "Bit" => ZMod 2

private theorem cubic_order : orderOf cubic = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime cubic_pow_three (by decide +kernel)

private theorem cubic_root (a : F) :
    cubic * upper a * cubic⁻¹ = upper (QuadraticAlgebra.omega^2*a) := by
  revert a
  decide +kernel

private theorem cubic_moves_root (a : F) (ha : upper a ≠ 1) :
    cubic * upper a * cubic⁻¹ ≠ upper a := by
  revert a
  decide +kernel

private theorem cubic_plane (v : V) (hv : v ∈ upperFixed) :
    action cubic v ∈ upperFixed := by
  rw [mem_upperFixed] at hv ⊢
  revert v
  decide +kernel

/-- The natural extension supplies its own cubic while retaining the exact
four-group, plane, and complete natural action. -/
public theorem exists_marked_embedding_with_cubic
    (R : Subgroup (Sp Bit)) (W : Submodule Bit (Vector Bit))
    (hR : Nat.card R = 4) (hW : Module.finrank Bit W = 2)
    (hiW : ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0)
    (hfR : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W) :
    ∃ e : V ≃ₗ[Bit] Vector Bit, ∃ ι : SL →* Sp Bit,
      Function.Injective ι ∧
      (∀ g v, ι g • e v = e (action g v)) ∧
      U0.map ι = R ∧ upperFixed.map e.toLinearMap = W ∧
      orderOf (ι cubic) = 3 ∧ ι cubic ∈ Subgroup.normalizer (R : Set (Sp Bit)) ∧
      (∀ r ∈ R, r ≠ 1 → ι cubic * r * (ι cubic)⁻¹ ≠ r) ∧
      (∀ v ∈ W, ι cubic • v ∈ W) ∧
      (∀ v : Vector Bit, ι cubic • v = v → v = 0) := by
  obtain ⟨e,ι,hι,hm,hRι,hWι⟩ := exists_marked_embedding R W hR hW hiW hfR
  refine ⟨e,ι,hι,hm,hRι,hWι,?_,?_,?_,?_,?_⟩
  · exact (orderOf_injective ι hι cubic).trans cubic_order
  · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (ι cubic)).injective])
    rintro x ⟨r,hr,rfl⟩
    rw [←hRι] at hr ⊢
    obtain ⟨a,ha,rfl⟩ := hr
    obtain ⟨b,rfl⟩ := (mem_U0 a).mp ha
    refine ⟨upper (QuadraticAlgebra.omega^2*b), (mem_U0 _).mpr ⟨_,rfl⟩, ?_⟩
    change ι (upper _) = ι cubic * ι (upper b) * (ι cubic)⁻¹
    rw [←map_inv, ←map_mul, ←map_mul, cubic_root]
  · intro r hr hr1 hh
    rw [←hRι] at hr
    obtain ⟨a,ha,rfl⟩ := hr
    obtain ⟨b,rfl⟩ := (mem_U0 a).mp ha
    have hb : upper b ≠ 1 := by intro he; simp [he] at hr1
    apply cubic_moves_root b hb
    apply hι
    simpa only [map_mul,map_inv] using hh
  · intro v hv
    rw [←hWι] at hv ⊢
    obtain ⟨u,hu,rfl⟩ := hv
    exact ⟨action cubic u, cubic_plane u hu, (hm cubic u).symm⟩
  · intro v hv
    obtain ⟨u,rfl⟩ := e.surjective v
    rw [hm] at hv
    have hu := cubic_fixed_eq_zero cubic cubic_order u (e.injective hv)
    simp [hu]

end Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
