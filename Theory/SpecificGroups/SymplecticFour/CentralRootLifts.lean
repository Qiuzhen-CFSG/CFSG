module

public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.GroupTheory.Commutator.ScalarInvariantRoot
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Lifting the eight symplectic root groups through central extensions

For finite characteristic-two fields of order greater than four, the full
scalar action of the root torus kills the commutator pairing of arbitrary
root lifts. The full root preimage is therefore abelian. Choose a torus
scalar c different from one: commutating a lift of t/(c-1) with a lift of
that torus element constructs a homomorphic section of the root group.
These eight additive sections generate every perfect central cover.

This is local input to the Sp₄(2ⁿ) multiplier computation in
Aschbacher–Smith, I.1.3, printed p.407 (PDF p.418), using the matrix roots
and torus weights of `RootSubgroup` and `RootTori`. It does not prove that
relations between different roots lift, or that the cover kernel is trivial.
The field of order four requires a separate argument.
-/

public section

open scoped IsMulCommutative commutatorElement
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour

namespace Theory.SpecificGroups.SymplecticFour.CentralRootLifts
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Root-torus commutators prove perfectness of the actual matrix group. -/
theorem perfect (hF : 2 < Nat.card F) : Group.IsPerfect (Sp F) := by
  constructor
  apply eq_top_of_rootElement_mem
  intro r t
  have hle : RootSubgroup.group (F := F) r ≤ commutator (Sp F) := by
    rw [← RootTori.commutator_eq r hF]
    exact Subgroup.commutator_mono le_top le_top
  exact hle ((RootSubgroup.mem_group_iff r _).mpr ⟨t, rfl⟩)

/-- Arbitrary lifts of two elements in the same root subgroup commute. -/
theorem root_preimage_commute (hF : 4 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 8) {v w : E}
    (hv : f v ∈ RootSubgroup.group r) (hw : f w ∈ RootSubgroup.group r) :
    Commute v w := by
  rw [RootSubgroup.group_eq_range] at hv hw
  apply CentralExtension.commute_lifts_of_full_scalar_action hF f hf hk
    (RootSubgroup.parameter r) ?_ hv hw
  intro c hc
  obtain ⟨s, hs⟩ := RootTori.weight_surjective r (Units.mk0 c hc)
  refine ⟨RootTori.element r s, fun x => ?_⟩
  change RootTori.element r s * rootElement r x * (RootTori.element r s)⁻¹ = _
  rw [RootTori.conjugate, hs]
  rfl

/-- Each of the eight additive matrix root groups lifts homomorphically. -/
theorem exists_root_lift (hF : 4 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 8) :
    ∃ u : Multiplicative F →* E, f.comp u = RootSubgroup.parameter r := by
  classical
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  have hc1 : (c : F) ≠ 1 := fun h => hc (Units.ext h)
  obtain ⟨t, ht⟩ := RootTori.weight_surjective r c
  obtain ⟨a, ha⟩ := hf (RootTori.element r t)
  choose b hb using fun x : F => hf (rootElement r x)
  let d : F := (c : F) - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr hc1
  let s : F → E := fun x => ⁅a, b (d⁻¹ * x)⁆
  have hs (x : F) : f (s x) = rootElement r x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, ha, hb, RootTori.conjugate, ht]
    have hinv (z : F) : (rootElement r z)⁻¹ = rootElement r (-z) := by
      exact ((RootSubgroup.parameter (F := F) r).map_inv (Multiplicative.ofAdd z)).symm
    rw [hinv, RootSubgroup.element_add]
    congr 1
    calc
      (c : F) * (d⁻¹ * x) + -(d⁻¹ * x) = d * (d⁻¹ * x) := by dsimp [d]; ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [mul_zero]
    have h0 : f (b 0) = f 1 := by rw [hb, RootSubgroup.element_zero, map_one]
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : F) : s (x + y) = s x * s y := by
    have hsum : f (b (d⁻¹ * (x + y))) = f (b (d⁻¹ * x) * b (d⁻¹ * y)) := by
      rw [map_mul, hb, hb, hb, RootSubgroup.element_add, mul_add]
    have hcomm : Commute (b (d⁻¹ * x)) (s y) :=
      root_preimage_commute hF f hf hk r
        (by rw [hb]; exact (RootSubgroup.mem_group_iff r _).mpr ⟨_, rfl⟩)
        (by rw [hs]; exact (RootSubgroup.mem_group_iff r _).mpr ⟨_, rfl⟩)
    change ⁅a, b (d⁻¹ * (x + y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * b (d⁻¹ * x) * s y * (b (d⁻¹ * x))⁻¹ = _
    rw [mul_assoc (s x), hcomm.eq, ← mul_assoc, mul_assoc (s x * s y), mul_inv_cancel, mul_one]
  refine ⟨{
    toFun x := s x.toAdd
    map_one' := hs0
    map_mul' x y := hsadd x.toAdd y.toAdd }, ?_⟩
  apply MonoidHom.ext
  intro x
  exact hs x.toAdd

/-- The eight lifted additive root groups generate any perfect central cover.
Their compatibility is with the literal matrix root parametrizations. -/
theorem exists_generating_root_lifts (hF : 4 < Nat.card F)
    {E : Type*} [Group E] (f : PerfectCentralCovering.Cover E (Sp F)) :
    ∃ u : Fin 8 → Multiplicative F →* E,
      (∀ r, f.toMonoidHom.comp (u r) = RootSubgroup.parameter r) ∧
      Subgroup.closure (Set.range (fun p : Fin 8 × Multiplicative F => u p.1 p.2)) = ⊤ := by
  choose u hu using fun r => exists_root_lift hF f.toMonoidHom f.surjective f.ker_le_center r
  refine ⟨u, hu, ?_⟩
  let R := Subgroup.closure (Set.range (fun p : Fin 8 × Multiplicative F => u p.1 p.2))
  have hR : R.map f.toMonoidHom = ⊤ := by
    apply eq_top_of_rootElement_mem
    intro r t
    exact ⟨u r (.ofAdd t), Subgroup.subset_closure ⟨(r, .ofAdd t), rfl⟩,
      DFunLike.congr_fun (hu r) (.ofAdd t)⟩
  have hs : Function.Surjective (f.toMonoidHom.comp R.subtype) := by
    intro x
    have hx : x ∈ R.map f.toMonoidHom := by rw [hR]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, hyx⟩
  let : Group.IsPerfect E := f.isPerfect
  have ht := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f.toMonoidHom R.subtype hs f.ker_le_center
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := ht x
  exact y.property

end Theory.SpecificGroups.SymplecticFour.CentralRootLifts

end
