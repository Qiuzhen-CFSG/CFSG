module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField.TorusSections
import Mathlib.Tactic.Ring

/-!
# Torus-equivariant additive root lifts over prime fields

Every matrix root group over Fₚ is cyclic, so its full preimage in a central
extension is abelian. Commutating arbitrary lifts with a diagonal torus lift
constructs an additive root section. Independence of central commutators from
the choice of lifts makes that section equivariant under the whole torus.
A scalar with c² ≠ 1 exists for every p > 3, including p = 5.

Only the characteristic-independent torus matrix identities are reused from
`TwoPrimary.LargeField.TorusSections`. No multiplier bound is used.
Source: the root-lifting calculation behind GLS3 §6.1 and Aschbacher–Smith
I.1.1–4, printed pp.407–408.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
private theorem root_inverse {F : Type*} [Field F] (r : Fin 8) (t : F) :
    (rootElement r t)⁻¹ = rootElement r (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [RootSubgroup.element_add, add_neg_cancel, RootSubgroup.element_zero]

variable {p : ℕ} [Fact p.Prime]

theorem exists_unit_sq_ne_one (hp : 3 < p) : ∃ c : (ZMod p)ˣ, c^2 ≠ 1 := by
  classical
  have hcard : ({0, 1, -1} : Finset (ZMod p)).card < (Finset.univ : Finset (ZMod p)).card := by
    exact lt_of_le_of_lt Finset.card_le_three (by simpa using hp)
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨Units.mk0 c hc.1, ?_⟩
  intro h
  have hsq : c^2 = 1 := congrArg Units.val h
  exact (sq_eq_one_iff.mp hsq).elim hc.2.1 hc.2.2

/-- Cyclicity of a matrix root group makes its entire central preimage abelian. -/
theorem root_preimage_commute {E : Type*} [Group E]
    (f : E →* Sp (ZMod p)) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 8)
    {x y : E} (hx : f x ∈ (RootSubgroup.parameter r).range)
    (hy : f y ∈ (RootSubgroup.parameter r).range) : Commute x y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨t, ht⟩ := hf (rootElement r 1)
  have hpow (c : ZMod p) : f (t ^ c.val) = rootElement r c := by
    rw [map_pow, ht]
    change (RootSubgroup.parameter r (.ofAdd 1)) ^ c.val =
      RootSubgroup.parameter r (.ofAdd c)
    rw [← map_pow]
    congr 1
    change Multiplicative.ofAdd (c.val • (1 : ZMod p)) = .ofAdd c
    simp [nsmul_eq_mul]
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk
    (ha.symm.trans (hpow a.toAdd).symm) (hb.symm.trans (hpow b.toAdd).symm)]
  exact ((Commute.refl t).pow_pow _ _).commutator_eq

private theorem exists_nontrivial_weight (hp : 3 < p) (r : Fin 8) :
    ∃ a b : (ZMod p)ˣ, torusWeight r a b ≠ 1 := by
  obtain ⟨c,hc⟩ := exists_unit_sq_ne_one hp
  have hc1 : c ≠ 1 := fun h => hc (by rw [h, one_pow])
  have hci : c⁻¹^2 ≠ 1 := by
    intro h
    apply hc
    have H := congrArg Inv.inv h
    simpa only [inv_pow, inv_inv, inv_one] using H
  fin_cases r
  · exact ⟨c,1,by simpa [torusWeight] using hc⟩
  · exact ⟨c,1,by simpa [torusWeight] using hci⟩
  · exact ⟨1,c,by simpa [torusWeight] using hc⟩
  · exact ⟨1,c,by simpa [torusWeight] using hci⟩
  · exact ⟨c,1,by simpa [torusWeight] using hc1⟩
  · exact ⟨c,1,by simpa [torusWeight] using hc1⟩
  · exact ⟨c,1,by simpa [torusWeight] using hc1⟩
  · exact ⟨1,c,by simpa [torusWeight] using hc1⟩

/-- The eight root sections can each be normalized by every diagonal torus lift. -/
theorem exists_equivariant_root_lift (hp : 3 < p)
    {E : Type*} [Group E] (f : E →* Sp (ZMod p)) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 8) :
    ∃ u : Multiplicative (ZMod p) →* E,
      f.comp u = RootSubgroup.parameter r ∧
      ∀ (a b : (ZMod p)ˣ) (z : E), f z = diagonalTorus a b → ∀ t : ZMod p,
        z * u (.ofAdd t) * z⁻¹ = u (.ofAdd ((torusWeight r a b : ZMod p) * t)) := by
  obtain ⟨a,b,hab⟩ := exists_nontrivial_weight hp r
  obtain ⟨A,hA⟩ := hf (diagonalTorus a b)
  choose B hB using fun t : ZMod p => hf (rootElement r t)
  let d : ZMod p := (torusWeight r a b : ZMod p) - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr (fun h => hab (Units.ext h))
  let s : ZMod p → E := fun x => ⁅A, B (d⁻¹*x)⁆
  have hs (x : ZMod p) : f (s x) = rootElement r x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, hA, hB, diagonal_conjugate]
    rw [root_inverse, RootSubgroup.element_add]
    congr 1
    calc
      (torusWeight r a b : ZMod p) * (d⁻¹*x) + -(d⁻¹*x) = d*(d⁻¹*x) := by
        dsimp [d]; ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [mul_zero]
    have h0 : f (B 0) = f 1 := by rw [hB, RootSubgroup.element_zero, map_one]
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : ZMod p) : s (x+y) = s x * s y := by
    have hsum : f (B (d⁻¹*(x+y))) = f (B (d⁻¹*x) * B (d⁻¹*y)) := by
      rw [map_mul, hB, hB, hB, RootSubgroup.element_add, mul_add]
    have hcomm : Commute (B (d⁻¹*x)) (s y) := root_preimage_commute f hf hk r
      ⟨.ofAdd _, (hB _).symm⟩ ⟨.ofAdd _, (hs _).symm⟩
    change ⁅A, B (d⁻¹*(x+y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * B (d⁻¹*x) * s y * (B (d⁻¹*x))⁻¹ = _
    rw [mul_assoc (s x), hcomm.eq, ← mul_assoc, mul_assoc (s x * s y),
      mul_inv_cancel, mul_one]
  refine ⟨{ toFun := fun x => s x.toAdd
            map_one' := hs0
            map_mul' := fun x y => hsadd x.toAdd y.toAdd },
    MonoidHom.ext (fun x => hs x.toAdd), ?_⟩
  intro c e z hz x
  change z * s x * z⁻¹ = s ((torusWeight r c e : ZMod p) * x)
  dsimp [s]
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · rw [map_mul, map_mul, map_inv, hz, hA, (diagonal_commute c e a b).eq,
      mul_assoc, mul_inv_cancel, mul_one]
  · rw [map_mul, map_mul, map_inv, hz, hB, hB, diagonal_conjugate]
    congr 1
    ring

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
