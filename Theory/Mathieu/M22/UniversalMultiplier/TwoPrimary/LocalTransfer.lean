module

public import Theory.GroupTheory.PerfectCentralCoverLocalBound
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates

/-!
# The relative hexad kernel calculation needed for M₂₂

Central transfer embeds the whole two-group kernel of a perfect M₂₂ cover
in the derived kernel of the literal hexad preimage: the native stabilizer
has index 77. The remaining local calculation is specified by `HexadLiftBound`.
It concerns central extensions of the actual degree-22 hexad stabilizer in
which its specified natural A₆ complement lifts, and bounds only the derived
part of the kernel. The complement-lifting condition is essential.

The conditional consumer in `TwoPrimary` constructs that lift and applies
this transfer injection. No local multiplier bound is asserted here.
Source: Aschbacher–Smith I.1.1–3, printed p.407, and I.2.2(6), printed p.412.
-/

public section
namespace Sporadic.Mathieu.M22UniversalMultiplier
open PerfectCentralCovering Subgroup
universe u

/-- The relative local calculation: after the specified A₆ complement lifts,
the derived part of a central two-kernel over the hexad stabilizer has order
at most four. This is an explicit proof obligation, not a multiplier axiom. -/
@[expose] def HexadLiftBound : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (q : D →* m22HexadStabilizer),
    Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
    (∃ s : alternatingGroup (Fin 6) →* D,
      q.comp s = m22HexadSection m22Hexad123_mem) →
    Nat.card (q.ker ⊓ _root_.commutator D : Subgroup D) ≤ 4


/-- Transfer embeds the full two-primary kernel in the derived kernel of the
literal preimage of the native hexad stabilizer. -/
theorem kernel_card_le_hexad_derived_kernel
    {E : Type u} [Group E] [Finite E] (f : Cover E M22)
    (hp : IsPGroup 2 f.toMonoidHom.ker) :
    Nat.card f.toMonoidHom.ker ≤
      Nat.card ((f.toMonoidHom.subgroupComap m22HexadStabilizer).ker ⊓
        _root_.commutator (m22HexadStabilizer.comap f.toMonoidHom) :
        Subgroup (m22HexadStabilizer.comap f.toMonoidHom)) := by
  let : Group.IsPerfect E := f.isPerfect
  let P := m22HexadStabilizer.comap f.toMonoidHom
  let q := f.toMonoidHom.subgroupComap m22HexadStabilizer
  have hKP : f.toMonoidHom.ker ≤ P := by
    intro x hx
    change f.toMonoidHom x ∈ m22HexadStabilizer
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hi : ¬ 2 ∣ P.index := by
    have hh := m22HexadStabilizer.card_mul_index
    rw [m22HexadStabilizer_card, m22_order] at hh
    have hind : m22HexadStabilizer.index = 77 := by omega
    rw [show P.index = m22HexadStabilizer.index from
      index_comap_of_surjective _ f.surjective, hind]
    decide
  have hd := central_pSubgroup_le_commutator P f.toMonoidHom.ker hKP f.ker_le_center hp hi
  let i : f.toMonoidHom.ker → (q.ker ⊓ _root_.commutator P : Subgroup P) := fun x =>
    ⟨⟨x, hKP x.property⟩, ⟨Subtype.ext x.property, by
      have hx := hd x.property
      rw [← map_subtype_commutator] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have heq : y = ⟨x, hKP x.property⟩ := Subtype.ext hxy
      exact heq ▸ hy⟩⟩
  apply Nat.card_le_card_of_injective i
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : (q.ker ⊓ _root_.commutator P : Subgroup P) =>
    ((z : P) : E)) hxy)
end Sporadic.Mathieu.M22UniversalMultiplier
