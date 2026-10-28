module

public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Theory.GroupAction.FourPointFixedOrbit

/-!
# Odd actions on abelian index-three subgroups

The family of abelian index-three subgroups carries the actual automorphism
map action. If this family has one or four members, every odd subgroup of
its ambient normalizer fixes a member. On four points, an odd orbit has
size one or three, and the complement of a three-point orbit is fixed.
The resulting fixed subgroup is normalized in the ambient group, with
its original subtype embedding retained.

The cardinality alternative is an explicit premise here. The previously
proved upper bound of four does not suffice for the fixed-point argument.
This is a structural step toward GLS4, Chapter 4, Lemma 3.11(a), using
the degree-three analysis in Aschbacher–Smith A.3.21(c), printed pp.55–56.
-/

namespace MulAction
private theorem odd_four_fixed {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X]
    (hodd : Odd (Nat.card K)) (hfour : Nat.card X = 4) :
    ∃ x : X, ∀ k : K, k • x = x := by
  have hpos : 0 < Nat.card X := by omega
  have : Nonempty X := Nat.card_pos_iff.mp hpos |>.1
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y, _, hy⟩ := exists_fixed_point_three_coprime_orbit_of_card_four hfour (1 : K) x (one_smul _ _)
  have hoddo : Odd (Nat.card (orbit K y)) := by
    rw [Nat.card_coe_set_eq, ← index_stabilizer]
    exact hodd.of_dvd_nat (Subgroup.index_dvd_card _)
  have hbound : Nat.card (orbit K y) ≤ 4 := hfour ▸ Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hne : Nat.card (orbit K y) ≠ 3 := by
    intro h
    simp [h] at hy
  have hone : Nat.card (orbit K y) = 1 := by
    obtain ⟨n, hn⟩ := hoddo
    omega
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp (by simpa only [Nat.card_coe_set_eq] using hone)
  have hyz : y = z := by simpa [hz] using mem_orbit_self (M := K) y
  refine ⟨y, fun k => ?_⟩
  have hk : k • y ∈ orbit K y := mem_orbit _ _
  simpa [hz, ← hyz] using hk
end MulAction

namespace Subgroup
open scoped Pointwise
variable (G : Type*) [Group G]
/-- The actual abelian index-three subgroups, with no ambient invariance assumed. -/
@[expose] public def AbelianIndexThree := {A : Subgroup G // IsMulCommutative A ∧ A.index = 3}
public instance abelianIndexThreeFinite [Finite G] : Finite (AbelianIndexThree G) :=
  inferInstanceAs (Finite {A : Subgroup G // IsMulCommutative A ∧ A.index = 3})
public instance abelianIndexThreeMulAction : MulAction (MulAut G) (AbelianIndexThree G) where
  smul f A := ⟨A.val.map f.toMonoidHom, by
    let : IsMulCommutative A.val := A.property.1
    exact ⟨inferInstance, (A.val.index_map_equiv f).trans A.property.2⟩⟩
  one_smul A := Subtype.ext (by change A.val.map (MonoidHom.id G) = A.val; exact A.val.map_id)
  mul_smul f g A := Subtype.ext (by
    change A.val.map (f * g).toMonoidHom = (A.val.map g.toMonoidHom).map f.toMonoidHom
    rw [map_map]
    rfl)

variable {G} [Finite G]
/-- An odd ambient normalizer fixes a member when the family has one or four members. -/
public theorem exists_abelian_index_three_normalized_by_odd
    (L Q : Subgroup G) (hodd : Odd (Nat.card L))
    (hLQ : L ≤ normalizer Q)
    (hcard : Nat.card (AbelianIndexThree Q) = 1 ∨
      Nat.card (AbelianIndexThree Q) = 4) :
    ∃ A : Subgroup Q, IsMulCommutative A ∧ A.index = 3 ∧
      L ≤ normalizer (A.map Q.subtype) := by
  let f : L →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hLQ)
  let : MulAction L (AbelianIndexThree Q) := MulAction.compHom _ f
  have hf : ∃ A : AbelianIndexThree Q, ∀ g : L, g • A = A := by
    rcases hcard with hcard | hcard
    · have h := Nat.card_eq_one_iff_unique.mp hcard
      let : Subsingleton (AbelianIndexThree Q) := h.1
      obtain ⟨A⟩ := h.2
      exact ⟨A, fun _ => Subsingleton.elim _ _⟩
    · exact MulAction.odd_four_fixed hodd hcard
  obtain ⟨A, hA⟩ := hf
  refine ⟨A.val, A.property.1, A.property.2, ?_⟩
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  have he := congrArg (fun B : AbelianIndexThree Q => B.val.map Q.subtype) (hA ⟨g, hg⟩)
  change (A.val.map (f ⟨g, hg⟩).toMonoidHom).map Q.subtype = A.val.map Q.subtype at he
  rw [map_map] at he
  change (A.val.map Q.subtype).map (MulAut.conj g).toMonoidHom = _
  rw [map_map]
  exact he
end Subgroup
