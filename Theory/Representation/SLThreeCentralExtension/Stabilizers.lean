module

public import Theory.Representation.SLThreeCentralExtension.Sylow
public import Theory.Representation.PSL3Two.OrbitStabilizers
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Orbit and stabilizer data for a central natural four-space

The nonfixed vectors form a fourteen-point orbit. Its stabilizer has order
12 and embeds, over the original projection, into a natural-point S₄;
the unique index-two subgroup identifies it with A₄. A commuting actor
fixing one vector of this orbit fixes all fourteen, and additivity fixes
the central line too. No orbit or stabilizer conclusion is an input.

Source: Aschbacher--Smith, 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Point stabilizer for the given representation, without changing its action. -/
@[expose] def vectorStabilizer (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (v : V) : Subgroup BinaryLinearThree.Group where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ (a*b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change ρ a⁻¹ v = v
    have hh := congrArg (ρ a⁻¹) ha
    simpa only [ρ.inv_self_apply] using hh.symm

theorem vectorStabilizer_index
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group V) (v : V) :
    (vectorStabilizer ρ v).index = Nat.card (Set.range (fun g => ρ g v)) := by
  let : MulAction BinaryLinearThree.Group V := {
    smul := fun g w => ρ g w
    one_smul := fun w => LinearMap.congr_fun ρ.map_one w
    mul_smul := fun g h w => LinearMap.congr_fun (ρ.map_mul g h) w }
  exact MulAction.index_stabilizer BinaryLinearThree.Group v

variable [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
  (p : ρ.IntertwiningMap W) (z : V) (hz : z ≠ 0)
  (hker : ∀ x, p x = 0 ↔ x = 0 ∨ x = z)
  (hfix : ∀ g, ρ g z = z)
  (hdim : Module.finrank (ZMod 2) V = 4)
  (hind : ∀ A B : Submodule (ZMod 2) V,
    (∀ g v, v ∈ A → ρ g v ∈ A) →
    (∀ g v, v ∈ B → ρ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥)

include hz hker hdim in
theorem nonfixed_card : Nat.card {x : V // p x ≠ 0} = 14 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hV : Nat.card V = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    norm_num
  have hk : Nat.card p.toLinearMap.ker = 2 := by
    apply (Nat.card_eq_two_iff' (0 : p.toLinearMap.ker)).mpr
    refine ⟨⟨z,(hker z).mpr (Or.inr rfl)⟩, ?_, ?_⟩
    · intro h; exact hz (congrArg Subtype.val h)
    · intro x hx
      rcases (hker x).mp x.property with h | h
      · exact False.elim (hx (Subtype.ext h))
      · exact Subtype.ext h
  change ((p.toLinearMap.ker : Set V)ᶜ).ncard = 14
  rw [Set.ncard_compl]
  change Nat.card V - Nat.card p.toLinearMap.ker = 14
  rw [hV, hk]

include hz hker hfix hind in
omit [FiniteDimensional (ZMod 2) V] in
theorem nonfixed_orbit (x : V) (hx : p x ≠ 0) :
    Set.range (fun g => ρ g x) = {y | p y ≠ 0} := by
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    change p (ρ g x) ≠ 0
    rw [p.isIntertwining]
    intro he
    have hh := congrArg (W g⁻¹) he
    exact hx (by simpa only [W.inv_self_apply, map_zero] using hh)
  · exact transitive_outside_kernel ρ p z hz hker hfix hind x y hx

include hz hker hfix hdim hind in
theorem nonfixed_stabilizer_index (x : V) (hx : p x ≠ 0) :
    (vectorStabilizer ρ x).index = 14 := by
  rw [vectorStabilizer_index, nonfixed_orbit ρ p z hz hker hfix hind x hx]
  exact nonfixed_card ρ p z hz hker hdim

include hz hker hfix hdim hind in
theorem nonfixed_stabilizer_card (x : V) (hx : p x ≠ 0) :
    Nat.card (vectorStabilizer ρ x) = 12 := by
  have hh := (vectorStabilizer ρ x).card_mul_index
  rw [nonfixed_stabilizer_index ρ p z hz hker hfix hdim hind x hx,
    Matrix.PSL3Two.card_SL] at hh
  omega

include hz hker hfix hdim hind in
/-- The nonfixed stabilizer is the actual A₄ inside the natural-head point stabilizer. -/
def nonfixedStabilizerEquivAlternating (x : V) (hx : p x ≠ 0) :
    vectorStabilizer ρ x ≃* alternatingGroup (Fin 4) :=
  BinaryLinearThree.OrbitStabilizers.twelveEquivAlternating
    (vectorStabilizer ρ x) (p x) hx
    (fun g hg => by
      rw [BinaryLinearThree.OrbitStabilizers.mem_natural]
      rw [← p.isIntertwining, show ρ g x = x from hg])
    (nonfixed_stabilizer_card ρ p z hz hker hfix hdim hind x hx)

include hz hker hfix hdim hind in
/-- The stabilizer contains an actual four-group, in its original embedding. -/
theorem nonfixed_stabilizer_contains_four (x : V) (hx : p x ≠ 0) :
    ∃ E : Subgroup (vectorStabilizer ρ x), IsKleinFour E := by
  let e := nonfixedStabilizerEquivAlternating ρ p z hz hker hfix hdim hind x hx
  let E := (alternatingGroup.kleinFour (Fin 4)).map e.symm.toMonoidHom
  let f := e.symm.subgroupMap (alternatingGroup.kleinFour (Fin 4))
  refine ⟨E,?_⟩
  constructor
  · exact (Nat.card_congr f.toEquiv).symm.trans
      (alternatingGroup.kleinFour_card_of_card_eq_four (by simp))
  · exact (Monoid.exponent_eq_of_mulEquiv f).symm.trans
      (alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp))

include hz hker hfix hdim hind in
/-- The source centralizer image in the rank-four branch is nonabelian. -/
theorem nonfixed_stabilizer_not_commutative (x : V) (hx : p x ≠ 0) :
    ¬ IsMulCommutative (vectorStabilizer ρ x) := by
  let e := nonfixedStabilizerEquivAlternating ρ p z hz hker hfix hdim hind x hx
  intro hc
  have hn : ¬ ∀ a b : alternatingGroup (Fin 4), a*b = b*a := by decide +kernel
  apply hn
  intro a b
  have he := congrArg e ((isMulCommutative_iff.mp hc) (e.symm a) (e.symm b))
  simpa only [map_mul,e.apply_symm_apply] using he

include hz hker hfix hind in
omit [FiniteDimensional (ZMod 2) V] in
/-- A commuting additive actor fixing a nonfixed vector fixes the entire extension. -/
theorem commuting_fixer_eq_one (f : V →+ V)
    (hf : ∀ g y, f (ρ g y) = ρ g (f y))
    (x : V) (hx : p x ≠ 0) (hfx : f x = x) : ∀ y, f y = y := by
  have hnon : ∀ y, p y ≠ 0 → f y = y := by
    intro y hy
    obtain ⟨g,rfl⟩ := transitive_outside_kernel ρ p z hz hker hfix hind x y hx hy
    rw [hf,hfx]
  have hzker : p z = 0 := (hker z).mpr (Or.inr rfl)
  have hxz : p (x+z) ≠ 0 := by simpa only [map_add,hzker,add_zero] using hx
  have hfz : f z = z := by
    have hh := hnon (x+z) hxz
    rw [map_add,hfx] at hh
    exact add_left_cancel hh
  intro y
  by_cases hy : p y = 0
  · rcases (hker y).mp hy with rfl | rfl
    · exact f.map_zero
    · exact hfz
  · exact hnon y hy

end Representation.OneCohomology.SLThreeCentralExtension
