module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.SubspaceCodimensionLoss

/-!
# Displacement on a subspace with a common center

If the displacement of an element on an invariant subspace lies in a line,
its displacement on the whole space is at most one plus the codimension of
that subspace. In particular an element moving four dimensions cannot act
with a common displacement line on a subspace of codimension two.

This is the linear obstruction used after the equality case of F.9.16(2)
in Aschbacher--Smith, 14.6.24(2), printed p.1041. It applies to central
covers and does not require complementary covering subspaces.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The displacement rank is bounded by the dimension of any containing space. -/
theorem fixedCodim_zpowers_le_of_displacement_mem
    (ρ : Representation (ZMod 2) A V) (a : A) (Z : Submodule (ZMod 2) V)
    (hd : ∀ v, ρ a v - v ∈ Z) :
    fixedCodim ρ (zpowers a) ≤ Module.finrank (ZMod 2) Z := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  apply Submodule.finrank_mono
  rintro _ ⟨v,rfl⟩
  exact hd v

/-- A common displacement space on an invariant subspace bounds ambient
movement, with the exact codimension loss retained. -/
theorem fixedCodim_zpowers_le_codim_add_center
    (ρ : Representation (ZMod 2) A V) (W : Subrepresentation ρ)
    (a : A) (Z : Submodule (ZMod 2) V)
    (hd : ∀ v : W.toSubmodule, ρ a v - v ∈ Z) :
    fixedCodim ρ (zpowers a) ≤
      Module.finrank (ZMod 2) Z + Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) := by
  let Z' := Z.comap W.toSubmodule.subtype
  have hZ' : Module.finrank (ZMod 2) Z' ≤ Module.finrank (ZMod 2) Z := by
    have he : Module.finrank (ZMod 2) Z' =
        Module.finrank (ZMod 2) (W.toSubmodule ⊓ Z : Submodule (ZMod 2) V) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
    exact he.le.trans (Submodule.finrank_mono inf_le_right)
  have hsmall := fixedCodim_zpowers_le_of_displacement_mem W.toRepresentation a Z'
    (fun v => hd v)
  have hloss := fixedCodim_le_subrepresentation_add_codim ρ W (zpowers a)
  omega

/-- Four-dimensional movement rules out a displacement line on a subspace
of codimension at most two. -/
theorem no_line_displacement_of_four_le
    (ρ : Representation (ZMod 2) A V) (W : Subrepresentation ρ)
    (a : A) (Z : Submodule (ZMod 2) V)
    (hZ : Module.finrank (ZMod 2) Z ≤ 1)
    (hW : Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) ≤ 2)
    (ha : 4 ≤ fixedCodim ρ (zpowers a))
    (hd : ∀ v : W.toSubmodule, ρ a v - v ∈ Z) : False := by
  have := fixedCodim_zpowers_le_codim_add_center ρ W a Z hd
  omega

end Representation.BinaryOffender
