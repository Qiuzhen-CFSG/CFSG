module

public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.LocalTransfer
public import Theory.GroupTheory.DerivedKernelQuotient

/-!
# The two layers of a relative hexad kernel

For the original native hexad projection q, R is the full inverse image of
its pointwise kernel E₁₆. Its derived subgroup lies in ker(q), because the
native pointwise kernel is abelian. Quotienting the original group by [R,R]
therefore retains q and makes the full radical abelian.

The two explicit remaining calculations have different mathematical content:
`RadicalDerivedBound` bounds the invariant commutator pairing by two, and
`AbelianRadicalBound` bounds the derived kernel of an abelian radical by two
using the marked A₆ module cover. Neither is asserted in this module.
Their quotient assembly is proved in the parent `HexadBound` module.

Source: Aschbacher–Smith I.1.3(4), printed p.407, and the split native hexad
geometry of I.2.2(6), printed p.412. No prescribed center order is assumed.
-/

@[expose] public section
noncomputable section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Sporadic.Mathieu.M22UniversalMultiplier.HexadBound
universe u
variable {D : Type u} [Group D]

/-- The full inverse image of the literal pointwise hexad kernel. -/
def radical (q : D →* m22HexadStabilizer) : Subgroup D :=
  (m22SetAction m22Hexad123).ker.comap q

instance radical_normal (q : D →* m22HexadStabilizer) : (radical q).Normal :=
  (m22HexadKernel_normal m22Hexad123).comap q

/-- The commutator subgroup killed to make the full hexad radical abelian. -/
def radicalDerived (q : D →* m22HexadStabilizer) : Subgroup D :=
  ⁅radical q, radical q⁆

instance radicalDerived_normal (q : D →* m22HexadStabilizer) : (radicalDerived q).Normal :=
  inferInstanceAs (⁅radical q, radical q⁆.Normal)

theorem radicalDerived_le_ker (q : D →* m22HexadStabilizer) : radicalDerived q ≤ q.ker := by
  let : IsElementaryAbelian 2 (m22SetAction m22Hexad123).ker :=
    m22HexadKernel_elementaryAbelian m22Hexad123_mem
  apply commutator_le.mpr
  intro x hx y hy
  change q ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (setLike_mul_comm (s := (m22SetAction m22Hexad123).ker) hx hy)

theorem radicalDerived_le_derived (q : D →* m22HexadStabilizer) :
    radicalDerived q ≤ _root_.commutator D := commutator_mono le_top le_top

/-- The original hexad projection after killing the radical's derived subgroup. -/
def abelianProjection (q : D →* m22HexadStabilizer) :
    D ⧸ radicalDerived q →* m22HexadStabilizer :=
  QuotientGroup.lift (radicalDerived q) q (radicalDerived_le_ker q)

@[simp] theorem abelianProjection_mk (q : D →* m22HexadStabilizer) (x : D) :
    abelianProjection q (QuotientGroup.mk' (radicalDerived q) x) = q x := rfl

theorem abelianProjection_surjective (q : D →* m22HexadStabilizer)
    (hq : Function.Surjective q) : Function.Surjective (abelianProjection q) :=
  QuotientGroup.lift_surjective_of_surjective _ q hq _

theorem radical_abelianProjection (q : D →* m22HexadStabilizer) :
    radical (abelianProjection q) =
      (radical q).map (QuotientGroup.mk' (radicalDerived q)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (radicalDerived q) x
    exact ⟨d, hx, rfl⟩
  · rintro x ⟨d, hd, rfl⟩
    exact hd

theorem abelianProjection_radical_commutative (q : D →* m22HexadStabilizer) :
    IsMulCommutative (radical (abelianProjection q)) := by
  apply commutator_self_eq_bot_iff.mp
  rw [radical_abelianProjection, ← map_commutator]
  exact QuotientGroup.map_mk'_self (radicalDerived q)

/-- The pairing step, still to be supplied independently of the abelian-cover step. -/
def RadicalDerivedBound : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (q : D →* m22HexadStabilizer),
    Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
    (∃ s : alternatingGroup (Fin 6) →* D,
      q.comp s = m22HexadSection m22Hexad123_mem) →
    Nat.card (radicalDerived q) ≤ 2

/-- The module-cover step, for an abelian full inverse image of the natural four-space. -/
def AbelianRadicalBound : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (q : D →* m22HexadStabilizer),
    Function.Surjective q → q.ker ≤ center D → IsPGroup 2 q.ker →
    (∃ s : alternatingGroup (Fin 6) →* D,
      q.comp s = m22HexadSection m22Hexad123_mem) →
    IsMulCommutative (radical q) →
    Nat.card (q.ker ⊓ _root_.commutator D : Subgroup D) ≤ 2

end Sporadic.Mathieu.M22UniversalMultiplier.HexadBound
