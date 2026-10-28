module

public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking
public import Theory.Representation.PSL3Two.NaturalDualNormalizer

/-!
# The natural--dual axes obstruct full transitivity

The normalizer of the full binary natural--dual action can only preserve the
two coordinate axes, either separately or after exchanging them.  Thus a
normal extension of the marked `SL₃(2)` action cannot be transitive on all
nonzero vectors: a vector with both coordinates nonzero cannot lie in the
orbit of a nonzero axis vector.

This is the abstract normalizer step used by the Rudvalis Chapter 12 local
exclusion.  The concrete order-64 normalizer supplies the transitivity
hypothesis; this module supplies the representation-theoretic contradiction.
-/

public noncomputable section
open Subgroup Representation

namespace BinaryLinearThree.NaturalDual

/-- A vector lies on one of the natural or dual coordinate axes. -/
def axisUnion (x : Space) : Prop := x.1 = 0 ∨ x.2 = 0

theorem axisUnion_preserved_of_marking
    {H : Type*} [_root_.Group H]
    (η : Representation (ZMod 2) H Space)
    (K : Subgroup H) [K.Normal]
    (q : K →* Group) (hq : Function.Surjective q)
    (hη : ∀ k : K, η k = action (q k)) :
    ∀ h x, axisUnion x → axisUnion (η h x) := by
  obtain ⟨a, ha, _⟩ := exists_automorphism_marking η K q hq hη
  intro h x hx
  let t : Space ≃ₗ[ZMod 2] Space :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom h)
  have ht (g : Group) (z : Space) :
      t (action g z) = action (a h g) (t z) := by
    change η h (action g z) = action (a h g) (η h z)
    rw [ha h]
    exact autAction_covariance (a h) g z
  change axisUnion (t x)
  by_cases hi : a h ∈ MulAut.innerSubgroup Group
  · obtain ⟨g, hg⟩ := inner_operator (a h) t ht hi
    rcases hx with hx | hx
    · left
      have hx' : x = (0, x.2) := by
        apply Prod.ext
        · exact hx
        · rfl
      rw [hx', hg]
      change W g 0 = 0
      exact map_zero _
    · right
      have hx' : x = (x.1, 0) := by
        apply Prod.ext
        · rfl
        · exact hx
      rw [hx', hg]
      change W.dual g 0 = 0
      exact map_zero _
  · have hs := outer_swaps (a h) t ht hi
    rcases hx with hx | hx
    · right
      have hx' : x = (0, x.2) := by
        apply Prod.ext
        · exact hx
        · rfl
      rw [hx']
      exact hs.2 x.2
    · left
      have hx' : x = (x.1, 0) := by
        apply Prod.ext
        · rfl
        · exact hx
      rw [hx']
      exact hs.1 x.1

theorem no_transitive_marked_normalizer
    {H : Type*} [_root_.Group H]
    (η : Representation (ZMod 2) H Space)
    (K : Subgroup H) [K.Normal]
    (q : K →* Group) (hq : Function.Surjective q)
    (hη : ∀ k : K, η k = action (q k))
    (htrans : ∀ x y : Space, x ≠ 0 → y ≠ 0 → ∃ h : H, η h x = y) :
    False := by
  have hpres := axisUnion_preserved_of_marking η K q hq hη
  obtain ⟨v, hv⟩ := exists_ne (0 : Vector)
  obtain ⟨w, hw⟩ := exists_ne (0 : Module.Dual (ZMod 2) Vector)
  have haxis : (v, 0) ≠ (0 : Space) := by
    intro h
    exact hv (by simpa using congrArg Prod.fst h)
  have hmixed : (v, w) ≠ (0 : Space) := by
    intro h
    exact hv (by simpa using congrArg Prod.fst h)
  obtain ⟨h, hh⟩ := htrans (v, 0) (v, w) haxis hmixed
  have hm : axisUnion (v, w) := by
    rw [← hh]
    exact hpres h (v, 0) (Or.inr rfl)
  rcases hm with hm | hm
  · exact hv (by simpa using hm)
  · exact hw (by simpa using hm)

end BinaryLinearThree.NaturalDual
