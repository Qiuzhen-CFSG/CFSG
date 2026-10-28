module
public import Theory.Representation.ElementaryTwoFixedRank

/-!
# A degree bound from an elementary eight and small fixed spaces

A faithful elementary eight acting in odd characteristic, with every
nonidentity fixed space of dimension at most two, contains an inverter.
For another actor b, the fixed spaces of b and its product with the
inverter receive the injective map v ↦ (v + bv, v − bv). Their dimensions
therefore bound the original dimension by four.

This sharpens the linear step of Aschbacher--Smith A.1.28, printed p.26,
for the full M₂₂-cover comparison in 4.2.13, printed p.612.
-/

public noncomputable section
namespace Representation.ElementaryTwoFixedRank
variable {K A V : Type*} [Field K] [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Small involution fixed spaces bound the degree of a faithful elementary eight by four. -/
theorem finrank_le_four_of_card_eight
    (ρ : Representation K A V) (hρ : Function.Injective ρ) (h2 : (2 : K) ≠ 0)
    (hfix : ∀ a : A, a ≠ 1 → Module.finrank K (Module.End.eigenspace (ρ a) 1) ≤ 2)
    (hcard : Nat.card A = 8) : Module.finrank K V ≤ 4 := by
  classical
  obtain ⟨a,ha,hai⟩ := (card_le_eight_and_inverter ρ hρ h2 hfix).2 hcard
  let : Fintype A := Fintype.ofFinite A
  have hb : ∃ b : A, b ≠ 1 ∧ b ≠ a := by
    by_contra! hh
    have hs : (Finset.univ : Finset A) ⊆ {1,a} := by
      intro b _
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact eq_or_ne b 1 |>.imp_right (hh b)
    have hc := Finset.card_le_card hs
    have hu : (Finset.univ : Finset A).card = 8 := by simpa [Nat.card_eq_fintype_card] using hcard
    have hc2 : ({1,a} : Finset A).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    omega
  obtain ⟨b,hb1,hba⟩ := hb
  have hab : a * b ≠ 1 := by
    intro he
    have hb : b = a := by
      calc
        b = a * (a * b) := by rw [←mul_assoc,←pow_two,
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 A) a,one_mul]
        _ = a := by rw [he,mul_one]
    exact hba hb
  have hbb (v : V) : ρ b (ρ b v) = v := by
    have hb2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) b
    have hh := congrArg (fun r : Module.End K V => r v) (show ρ b * ρ b = 1 by
      rw [←map_mul,←pow_two,hb2,map_one])
    exact hh
  let P := Module.End.eigenspace (ρ b) 1
  let N := Module.End.eigenspace (ρ (a*b)) 1
  let f : V →ₗ[K] P × N := {
    toFun := fun v => (⟨v + ρ b v, by
      rw [Module.End.mem_eigenspace_iff,one_smul,map_add,hbb,add_comm]⟩,
      ⟨v - ρ b v, by
        rw [Module.End.mem_eigenspace_iff,one_smul,map_mul]
        change ρ a (ρ b (v - ρ b v)) = v - ρ b v
        rw [hai,map_sub,hbb,neg_sub]⟩)
    map_add' := by
      intro v w
      apply Prod.ext
      · apply Subtype.ext
        change v+w+ρ b (v+w) = (v+ρ b v)+(w+ρ b w)
        rw [map_add]
        abel
      · apply Subtype.ext
        change v+w-ρ b (v+w) = (v-ρ b v)+(w-ρ b w)
        rw [map_add]
        abel
    map_smul' := by intro c v; ext <;> simp [map_smul,smul_add,smul_sub] }
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hp : v + ρ b v = 0 := congrArg (fun z : P × N => (z.1 : V)) hv
    have hn : v - ρ b v = 0 := congrArg (fun z : P × N => (z.2 : V)) hv
    have hz : (2 : K) • v = 0 := by
      calc
        _ = (v + ρ b v) + (v - ρ b v) := by rw [two_smul]; abel
        _ = 0 := by rw [hp,hn,add_zero]
    exact (smul_eq_zero.mp hz).resolve_left h2
  have hd := LinearMap.finrank_le_finrank_of_injective hfi
  rw [Module.finrank_prod] at hd
  have hp := hfix b hb1
  have hn := hfix (a*b) hab
  change Module.finrank K V ≤ Module.finrank K P + Module.finrank K N at hd
  change Module.finrank K P ≤ 2 at hp
  change Module.finrank K N ≤ 2 at hn
  omega
end Representation.ElementaryTwoFixedRank
