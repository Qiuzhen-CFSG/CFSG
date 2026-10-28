module

public import Stellmacher.Recognition.FongWreathedInducingData

/-!
# The special support of Fong's actual inducing data

For an element Fⁱu with i odd, raising to the odd cardinal of U kills u
and leaves a generator of ⟨F⟩. Thus a transporter between two such elements
normalizes ⟨F⟩ and belongs to H. This discharges the special-support contract
for any inducing data linked to the actual Sylow coordinates; no simplicity
or solvable-centralizer hypothesis is needed for this step.

Source: P. Fong, Some Sylow subgroups of order 32 and a characterization
of U(3,3), J. Algebra 6 (1967), printed p. 72, the special classes D.
-/

public section

namespace Stellmacher.Recognition.FongWreathedInduction.InducingData
variable {G : Type*} [Group G] (d : InducingData G)

/-- The odd-core cardinal kills the odd part and leaves a generator of ⟨F⟩. -/
theorem support_power_generates (a : d.H) (ha : a ∈ d.support) :
    Subgroup.zpowers (a ^ Nat.card d.U) = Subgroup.zpowers d.f := by
  obtain ⟨i, hi, u, rfl⟩ := ha
  have hu : (u : d.H) ^ Nat.card d.U = 1 := by
    exact congrArg Subtype.val (pow_card_eq_one' (x := u))
  rw [((d.commute_U u).pow_left i.val).mul_pow, hu, mul_one, ← pow_mul]
  have hc : Nat.Coprime 8 (i.val * Nat.card d.U) := by
    change Nat.Coprime (2 ^ 3) _
    rw [Nat.coprime_pow_left_iff (by decide), Nat.coprime_two_left]
    exact hi.mul d.odd_U
  exact le_antisymm
    (Subgroup.zpowers_le.mpr ((Subgroup.zpowers d.f).pow_mem (Subgroup.mem_zpowers _) _))
    (Subgroup.zpowers_le.mpr (mem_zpowers_pow_iff.mpr (by rw [d.order_f]; exact hc.symm)))

/-- The same cyclic-subgroup recovery in the ambient group. -/
theorem support_power_generates_ambient (a : d.H) (ha : a ∈ d.support) :
    Subgroup.zpowers ((a : G) ^ Nat.card d.U) = Subgroup.zpowers (d.f : G) := by
  simpa only [MonoidHom.map_zpowers, map_pow, Subgroup.subtype_apply] using
    congrArg (Subgroup.map d.H.subtype) (d.support_power_generates a ha)

/-- Every actual normalizer witness has the required special transporters. -/
theorem hasSpecialSupport_of_isActual (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) (hd : d.IsActual S P) : d.HasSpecialSupport := by
  intro a b ha hb g hg
  have hp : g⁻¹ * (a : G) ^ Nat.card d.U * g = (b : G) ^ Nat.card d.U := by
    have h := congrArg (fun x : G => x ^ Nat.card d.U) hg
    rw [show g⁻¹ * (a : G) * g = g⁻¹ * (a : G) * (g⁻¹)⁻¹ by simp, conj_pow, inv_inv] at h
    exact h
  have hn : g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (d.f : G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq,
      ← d.support_power_generates_ambient a ha, MonoidHom.map_zpowers]
    change Subgroup.zpowers (g⁻¹ * (a : G) ^ Nat.card d.U * (g⁻¹)⁻¹) = _
    rw [inv_inv, hp, d.support_power_generates_ambient b hb,
      d.support_power_generates_ambient a ha]
  have hn' := (Subgroup.normalizer (Subgroup.zpowers (d.f : G) : Set G)).inv_mem hn
  simpa only [inv_inv, hd.2.1, ← hd.1] using hn'
end Stellmacher.Recognition.FongWreathedInduction.InducingData
