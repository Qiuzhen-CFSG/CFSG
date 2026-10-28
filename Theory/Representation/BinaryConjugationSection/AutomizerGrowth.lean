module
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Mathlib.GroupTheory.Index

/-!
# An outer actor enlarges a section automizer

Suppose P acts on V as a group of order four and centralizes B/Z, where B
lies in V and in the literal conjugation section P/Z. An actor in T moving
one vector of B/Z cannot induce on V an automorphism already induced by P.
The image of P is therefore proper in the image of T, whose order is at
least eight. The proof retains the original subgroup inclusions and actions.

Source: the automizer count in Aschbacher–Smith, E.2.17.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {H M : Type*} [Group H] [Finite H] [AddCommGroup M] [Module (ZMod 2) M]
  {T P Z : Subgroup H} {ρ : Representation (ZMod 2) T M}

/-- An actor moving a section image fixed by P lies outside P's induced
four-group, so the actual T-automizer has order at least eight. -/
theorem eight_le_automizer_of_moving_section
    (c : BinaryConjugationSection T P Z ρ) (V B : Subgroup H)
    (hTV : T ≤ normalizer (V : Set H)) (hBV : B ≤ V)
    (hc : ⁅P,B⁆ ≤ Z)
    (hfour : Nat.card ((P.subgroupOf T).map
      (V.normalizerMonoidHom.comp (inclusion hTV))) = 4)
    (g : T) (hmove : ∃ b : P, (b : H) ∈ B ∧
      ρ g (c.coordinates b).toAdd ≠ (c.coordinates b).toAdd) :
    8 ≤ Nat.card (V.normalizerMonoidHom.comp (inclusion hTV)).range := by
  let f := V.normalizerMonoidHom.comp (inclusion hTV)
  let A := (P.subgroupOf T).map f
  have hnot : f g ∉ A := by
    rintro ⟨p,hp,hpg⟩
    obtain ⟨b,hb,hbmove⟩ := hmove
    apply hbmove
    let bV : V := ⟨b,hBV hb⟩
    have he := congrArg (fun a : MulAut V => (a bV : H)) hpg
    change (p : H) * b * (p : H)⁻¹ = (g : H) * b * (g : H)⁻¹ at he
    have hcoord : (c.coordinates
        ⟨(g : H) * b * (g : H)⁻¹,
          (mem_normalizer_iff.mp (c.normalized g.property) b).mp b.property⟩).toAdd =
        (c.coordinates
        ⟨(p : H) * b * (p : H)⁻¹,
          (mem_normalizer_iff.mp (c.normalized p.property) b).mp b.property⟩).toAdd := by
      congr 2
      exact Subtype.ext he.symm
    rw [c.equivariant,c.equivariant] at hcoord
    exact hcoord.trans (c.fixed_on_imageSpace_of_commutator_le P B hc p hp _
      ((c.mem_imageSpace_iff B _).mpr ⟨b,hb,rfl⟩))
  have hlt : A < f.range := lt_of_le_of_ne (map_le_range f _) (fun he =>
    hnot (he.symm ▸ (show f g ∈ f.range from ⟨g,rfl⟩)))
  have hindex : 2 ≤ A.relIndex f.range := by
    have hzero : A.relIndex f.range ≠ 0 := (A.subgroupOf f.range).index_ne_zero_of_finite
    have hone : A.relIndex f.range ≠ 1 := fun h => hlt.not_ge (relIndex_eq_one.mp h)
    omega
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup (MulAut V)) A f.range bot_le hlt.le
  simp only [relIndex_bot_left] at hcard
  change Nat.card A = 4 at hfour
  change 8 ≤ Nat.card f.range
  rw [hfour] at hcard
  omega
end Representation.BinaryConjugationSection
