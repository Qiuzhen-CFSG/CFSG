module

public import Theory.Representation.SLThreeCentralExtension.Orbits
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Set.Card

/-!
# The fixed line of a Sylow subgroup in a natural SL₃ extension

The nonsplit four-dimensional natural extension has fourteen vectors outside
its fixed line and they form one orbit. A Sylow-fixed vector in that orbit
would have a stabilizer of odd index, whereas its orbit has even length.
Thus every Sylow-fixed vector lies in the original central kernel.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.8(2), printed p.91, used in 12.4.5–6, printed pp.813–814.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)

/-- A Sylow two-subgroup fixes exactly the central line in a nonsplit natural extension. -/
theorem sylow_fixed_eq_kernel
    (p : ρ.IntertwiningMap W) (z : V) (hz : z ≠ 0)
    (hker : ∀ x, p x = 0 ↔ x = 0 ∨ x = z)
    (hfix : ∀ g, ρ g z = z)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hind : ∀ A B : Submodule (ZMod 2) V,
      (∀ g v, v ∈ A → ρ g v ∈ A) →
      (∀ g v, v ∈ B → ρ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥)
    (T : Sylow 2 BinaryLinearThree.Group) :
    fixedSpace ρ (T : Subgroup BinaryLinearThree.Group) = p.toLinearMap.ker := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : MulAction BinaryLinearThree.Group V := {
    smul := fun g v => ρ g v
    one_smul := by intro v; exact LinearMap.congr_fun ρ.map_one v
    mul_smul := by intro g h v; exact LinearMap.congr_fun (ρ.map_mul g h) v }
  have hV : Nat.card V = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    norm_num
  have hkerz : z ∈ p.toLinearMap.ker := (hker z).mpr (Or.inr rfl)
  have hk : Nat.card p.toLinearMap.ker = 2 := by
    apply (Nat.card_eq_two_iff' (0 : p.toLinearMap.ker)).mpr
    refine ⟨⟨z,hkerz⟩, ?_, ?_⟩
    · intro h; exact hz (congrArg Subtype.val h)
    · intro x hx
      rcases (hker x).mp x.property with h | h
      · exact False.elim (hx (Subtype.ext h))
      · exact Subtype.ext h
  apply le_antisymm
  · intro x hx
    change p x = 0
    by_contra hpx
    have ho : MulAction.orbit BinaryLinearThree.Group x =
        (p.toLinearMap.ker : Set V)ᶜ := by
      ext y
      rw [MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨g, rfl⟩
        change p (ρ g x) ≠ 0
        rw [p.isIntertwining]
        intro he
        apply hpx
        have he' := congrArg (W g⁻¹) he
        simpa only [W.inv_self_apply, map_zero] using he'
      · intro hy
        exact transitive_outside_kernel ρ p z hz hker hfix hind x y hpx hy
    have hc : (MulAction.orbit BinaryLinearThree.Group x).ncard = 14 := by
      rw [ho, Set.ncard_compl]
      change Nat.card V - Nat.card p.toLinearMap.ker = 14
      rw [hV, hk]
    have hT : (T : Subgroup BinaryLinearThree.Group) ≤
        MulAction.stabilizer BinaryLinearThree.Group x := by
      intro t ht
      exact hx ⟨t,ht⟩
    apply T.not_dvd_index
    apply (show 2 ∣ (MulAction.stabilizer BinaryLinearThree.Group x).index from ?_).trans
      (index_dvd_of_le hT)
    rw [MulAction.index_stabilizer, hc]
    norm_num
  · intro x hx t
    rcases (hker x).mp hx with rfl | rfl
    · exact map_zero _
    · exact hfix t
end Representation.OneCohomology.SLThreeCentralExtension
