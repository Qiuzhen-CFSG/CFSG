module
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Transporting an orbit through matched point stabilizers

Suppose a homomorphism pulls one point stabilizer back to another. If the
image of a subgroup is transitive away from the target base point, the
subgroup is transitive on the source orbit away from its base point.
For two orbit representatives g and h, lift the target actor t; then
h⁻¹tg fixes the base point on both sides. No faithfulness or surjectivity
of the whole homomorphism is needed.

This is the orbit transport used for the local linear action in DGS,
Groups and Graphs (1985), proof of 12.3(a), printed p.179.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupAction.MatchedPointOrbit
variable {A B X Y : Type*} [Group A] [Group B] [MulAction A X] [MulAction B Y]

/-- Equal inverse-image stabilizers transfer transitivity away from the base point
to the corresponding source orbit, with actors lifted in the specified subgroup. -/
theorem transitive_away_from_base (f : A →* B) (D : Subgroup A) (x : X) (p : Y)
    (hstab : (MulAction.stabilizer B p).comap f = MulAction.stabilizer A x)
    (htrans : ∀ a b : Y, a ≠ p → b ≠ p → ∃ t ∈ D.map f, t • a = b)
    (g h : A) (hg : g • x ≠ x) (hh : h • x ≠ x) :
    ∃ t ∈ D, t • (g • x) = h • x := by
  have hpoint (a : A) (ha : a • x ≠ x) : f a • p ≠ p := by
    intro he
    apply ha
    have hm : a ∈ (MulAction.stabilizer B p).comap f := he
    rwa [hstab] at hm
  obtain ⟨_, ⟨t, ht, rfl⟩, he⟩ := htrans (f g • p) (f h • p) (hpoint g hg) (hpoint h hh)
  have hm : h⁻¹ * t * g ∈ (MulAction.stabilizer B p).comap f := by
    change f (h⁻¹ * t * g) • p = p
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, he, inv_smul_smul]
  rw [hstab] at hm
  have hx : (h⁻¹ * t * g) • x = x := hm
  refine ⟨t, ht, ?_⟩
  have hhx := congrArg (fun y : X => h • y) hx
  simpa only [mul_smul, smul_inv_smul] using hhx

end Theory.GroupAction.MatchedPointOrbit
