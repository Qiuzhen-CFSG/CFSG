module

public import Theory.SpecificGroups.PSL3Two.PairedGraphInputs
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
import Mathlib.Tactic.Group

/-!
# Arbitrary outer involutions of SL₃(2)

Every outer involution of the actual binary special linear group is conjugate
by an inner automorphism to the specified diagram involution. The square
identity and centerlessness first give a diagram cocycle; the proved cocycle
calculation then supplies the conjugator. Transport by that inner map gives
coboundary witnesses for the original automorphism and identifies its actual
fixed subgroup with S₃.

These are the single-factor inputs for the paired-group centralizer bounds
in Aschbacher--Smith, Lemma 2.4.34, combined manuscript of 1 March 2004,
printed p.548. No compatibility with a separately chosen Sylow subgroup is
assumed in this transport.
-/

public section
namespace Matrix.PSL3Two.PairedOuterInputs
open MarkedAutomorphisms
private theorem inner_graph_cocycle {G : Type*} [Group G] (δ β : MulAut G)
    (hδ : Function.Involutive δ) (hβ : Function.Involutive β)
    (hc : Function.Injective (MulAut.conj : G →* MulAut G))
    (g : G) (hg : β = MulAut.conj g * δ) : g * δ g = 1 := by
  apply hc
  rw [map_one]
  have he : MulAut.conj (g * δ g) = β * β := by
    rw [hg]
    ext x : 1
    change (g * δ g) * x * (g * δ g)⁻¹ = g * δ (g * δ x * g⁻¹) * g⁻¹
    rw [map_mul, map_mul, map_inv, hδ x]
    group
  rw [he]
  ext x : 1
  exact hβ x
private theorem conjugate_of_coboundary {G : Type*} [Group G]
    (δ β : MulAut G) (g h : G)
    (hg : β = MulAut.conj g * δ)
    (hh : h * g * (δ h)⁻¹ = 1) :
    MulAut.conj h * β * (MulAut.conj h)⁻¹ = δ := by
  rw [hg]
  ext x : 1
  change h * (g * δ (h⁻¹ * x * h) * g⁻¹) * h⁻¹ = δ x
  simp only [map_mul, map_inv]
  calc
    h * (g * ((δ h)⁻¹ * δ x * δ h) * g⁻¹) * h⁻¹ =
      (h * g * (δ h)⁻¹) * δ x * (h * g * (δ h)⁻¹)⁻¹ := by group
    _ = δ x := by rw [hh]; simp
private theorem compatible_of_conjugate (β : MulAut SL) (h : SL)
    (hh : MulAut.conj h * β * (MulAut.conj h)⁻¹ = diagram) (x : SL) :
    MulAut.conj h (β x) = diagram (MulAut.conj h x) := by
  have he := MulEquiv.congr_fun hh (MulAut.conj h x)
  simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using he


/-- An arbitrary outer involution is inner-conjugate to the marked diagram map. -/
theorem exists_inner_conjugate_diagram (β : MulAut SL) (hβ : Function.Involutive β)
    (hout : ∀ g, β ≠ MulAut.conj g) :
    ∃ h : SL, MulAut.conj h * β * (MulAut.conj h)⁻¹ = diagram := by
  obtain ⟨g, hg | hg⟩ := inner_or_graph β
  · exact False.elim (hout g hg)
  · obtain ⟨h, hh⟩ := PairedGraphInputs.exists_coboundary g
      (inner_graph_cocycle diagram β diagram_involutive hβ
        MarkedAutomorphisms.conj_injective g hg)
    exact ⟨h, conjugate_of_coboundary diagram β g h hg hh⟩

/-- Each cocycle for the original outer involution has an actual coboundary witness. -/
theorem exists_coboundary_of_outer (β : MulAut SL) (hβ : Function.Involutive β)
    (hout : ∀ g, β ≠ MulAut.conj g) (a : SL) (ha : a * β a = 1) :
    ∃ b : SL, b * a * (β b)⁻¹ = 1 := by
  obtain ⟨h, hh⟩ := exists_inner_conjugate_diagram β hβ hout
  let e := MulAut.conj h
  have he (x : SL) : e (β x) = diagram (e x) := compatible_of_conjugate β h hh x
  have hec : e a * diagram (e a) = 1 := by rw [← he, ← map_mul, ha, map_one]
  obtain ⟨c,hc⟩ := PairedGraphInputs.exists_coboundary (e a) hec
  refine ⟨e.symm c, e.injective ?_⟩
  simpa only [map_mul, map_inv, map_one, he, e.apply_symm_apply] using hc

/-- The fixed subgroup of the original outer involution is the symmetric group on three letters. -/
noncomputable def fixedEquivOfOuter (β : MulAut SL) (hβ : Function.Involutive β)
    (hout : ∀ g, β ≠ MulAut.conj g) : β.fixedSubgroup ≃* Equiv.Perm (Fin 3) := by
  let h := Classical.choose (exists_inner_conjugate_diagram β hβ hout)
  have hh := Classical.choose_spec (exists_inner_conjugate_diagram β hβ hout)
  exact (MulAut.fixedSubgroupEquivOfCompatible (MulAut.conj h) β diagram
    (compatible_of_conjugate β h hh)).trans PairedGraphInputs.fixedEquivSymmetricThree

/-- The literal fixed subgroup of any outer involution has order six. -/
theorem card_fixed_of_outer (β : MulAut SL) (hβ : Function.Involutive β)
    (hout : ∀ g, β ≠ MulAut.conj g) : Nat.card β.fixedSubgroup = 6 := by
  exact (Nat.card_congr ((fixedEquivOfOuter β hβ hout).trans
    PairedGraphInputs.fixedEquivSymmetricThree.symm).toEquiv).trans
      PairedGraphInputs.card_fixedSubgroup

end Matrix.PSL3Two.PairedOuterInputs
