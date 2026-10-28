module

public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Sign-character spaces for ternary octonion automorphisms

These are the actual simultaneous eigenspaces in the eight-dimensional
split-octonion representation. Products multiply characters. Different
characters are orthogonal for the norm, and multiplication by a nonisotropic
homogeneous vector identifies the corresponding character spaces.

The lemmas do not assume involution conjugacy or a classification of elementary
subgroups. In particular, the spanning hypothesis in the nondegeneracy lemma
remains an explicit representation-theoretic obligation.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), pp.3–4 and 481–482. Coordinates use the licensed ATLAS
split-octonion port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.CharacterGeometry
open Atlas.SplitOctonion

abbrev G := Model (ZMod 3)
abbrev V := Carrier (ZMod 3)
abbrev Character (E : Subgroup G) := E →* (ZMod 3)ˣ

/-- The simultaneous character space for the actual subgroup action. -/
def characterSpace (E : Subgroup G) (χ : Character E) : Submodule (ZMod 3) V where
  carrier := {v | ∀ g : E, g.val.val v = (χ g : ZMod 3) • v}
  zero_mem' := by intro g; simp
  add_mem' hx hy := by intro g; simp only [map_add, hx g, hy g, smul_add]
  smul_mem' r x hx := by intro g; rw [map_smul, hx g, smul_comm]

@[simp] theorem mem_characterSpace (E : Subgroup G) (χ : Character E) (v : V) :
    v ∈ characterSpace E χ ↔ ∀ g : E, g.val.val v = (χ g : ZMod 3) • v := Iff.rfl

theorem unit_mem (E : Subgroup G) : unit ∈ characterSpace E 1 := by
  intro g; simp

theorem character_mul_self {E : Subgroup G} (χ : Character E) : χ * χ = 1 := by
  apply MonoidHom.ext
  intro g
  exact (by decide +kernel : ∀ u : (ZMod 3)ˣ, u*u = 1) (χ g)

theorem mul_mem {E : Subgroup G} {χ ψ : Character E} {x y : V}
    (hx : x ∈ characterSpace E χ) (hy : y ∈ characterSpace E ψ) :
    mul x y ∈ characterSpace E (χ * ψ) := by
  intro g
  rw [automorphism_mul, hx g, hy g, smul_mul, SplitOctonion.mul_smul, smul_smul]
  rfl

theorem conjugate_mem {E : Subgroup G} {χ : Character E} {v : V}
    (hv : v ∈ characterSpace E χ) : conjugate v ∈ characterSpace E χ := by
  intro g
  rw [automorphism_conjugate, hv g, conjugate_smul]

/-- Distinct simultaneous character spaces are norm-orthogonal. -/
theorem orthogonal {E : Subgroup G} {χ ψ : Character E} (hne : χ ≠ ψ)
    {x y : V} (hx : x ∈ characterSpace E χ) (hy : y ∈ characterSpace E ψ) :
    normPolar x y = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : E, χ g ≠ ψ g := by
    by_contra h
    apply hne
    apply MonoidHom.ext
    intro g
    exact not_not.mp (fun hn => h ⟨g, hn⟩)
  have hcoeff : (χ g : ZMod 3) * (ψ g : ZMod 3) - 1 ≠ 0 :=
    (by decide +kernel : ∀ a b : (ZMod 3)ˣ, a ≠ b → (a : ZMod 3)*(b : ZMod 3)-1 ≠ 0)
      (χ g) (ψ g) hg
  have hp := automorphism_normPolar g.val x y
  rw [hx g, hy g] at hp
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hp
  apply (mul_eq_zero.mp (show ((χ g : ZMod 3)*(ψ g : ZMod 3)-1)*normPolar x y = 0 from ?_)).resolve_left hcoeff
  rw [sub_mul, one_mul, mul_comm (χ g : ZMod 3), _root_.mul_assoc, hp, sub_self]

/-- Restrict right multiplication by a nonisotropic character vector. -/
def characterSpaceMulEquiv {E : Subgroup G} {χ : Character E}
    (v : V) (hv : v ∈ characterSpace E χ) (hn : norm v ≠ 0) (ψ : Character E) :
    characterSpace E ψ ≃ₗ[ZMod 3] characterSpace E (ψ * χ) where
  toFun x := ⟨mul x.val v, mul_mem x.property hv⟩
  invFun y := ⟨(norm v)⁻¹ • mul y.val (conjugate v), by
    have hm := mul_mem y.property (conjugate_mem hv)
    rw [_root_.mul_assoc ψ χ χ, character_mul_self χ, _root_.mul_one ψ] at hm
    exact (characterSpace E ψ).smul_mem _ hm⟩
  left_inv x := by
    apply Subtype.ext
    exact (rightMulEquiv v hn).left_inv x.val
  right_inv y := by
    apply Subtype.ext
    exact (rightMulEquiv v hn).right_inv y.val
  map_add' x y := by apply Subtype.ext; exact add_mul x.val y.val v
  map_smul' r x := by apply Subtype.ext; exact smul_mul r x.val v

theorem finrank_mul {E : Subgroup G} {χ : Character E}
    (v : V) (hv : v ∈ characterSpace E χ) (hn : norm v ≠ 0) (ψ : Character E) :
    Module.finrank (ZMod 3) (characterSpace E ψ) =
      Module.finrank (ZMod 3) (characterSpace E (ψ * χ)) :=
  (characterSpaceMulEquiv v hv hn ψ).finrank_eq

/-- Spanning and orthogonality make each character space nondegenerate. -/
theorem nondegenerate_of_span (E : Subgroup G)
    (hspan : (⨆ χ : Character E, characterSpace E χ) = ⊤)
    (χ : Character E) {x : V} (hx : x ∈ characterSpace E χ)
    (h : ∀ y ∈ characterSpace E χ, normPolar x y = 0) : x = 0 := by
  apply normPolar_nondegenerate
  intro y
  have hy : y ∈ ⨆ ψ : Character E, characterSpace E ψ := by rw [hspan]; trivial
  refine Submodule.iSup_induction _ (motive := fun z => normPolar x z = 0) hy ?_ ?_ ?_
  · intro ψ z hz
    by_cases he : χ = ψ
    · subst ψ; exact h z hz
    · exact orthogonal he hx hz
  · exact map_zero _
  · intro u v hu hv
    rw [map_add, hu, hv, add_zero]

/-- Every nonzero character space has a nonisotropic vector, once spanning
has been established. -/
theorem exists_nonisotropic_of_span (E : Subgroup G)
    (hspan : (⨆ χ : Character E, characterSpace E χ) = ⊤)
    (χ : Character E) (hne : characterSpace E χ ≠ ⊥) :
    ∃ v ∈ characterSpace E χ, norm v ≠ 0 := by
  by_contra hn
  have hz : ∀ v ∈ characterSpace E χ, norm v = 0 := by
    intro v hv
    exact not_not.mp (fun h => hn ⟨v, hv, h⟩)
  apply hne
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply nondegenerate_of_span E hspan χ hx
  intro y hy
  rw [normPolar_eq, hz _ ((characterSpace E χ).add_mem hx hy), hz _ hx, hz _ hy]
  simp

/-- The occurring characters are closed under multiplication. -/
theorem mul_ne_bot_of_span (E : Subgroup G)
    (hspan : (⨆ χ : Character E, characterSpace E χ) = ⊤)
    {χ ψ : Character E} (hχ : characterSpace E χ ≠ ⊥)
    (hψ : characterSpace E ψ ≠ ⊥) : characterSpace E (χ * ψ) ≠ ⊥ := by
  obtain ⟨x, hx, hn⟩ := exists_nonisotropic_of_span E hspan χ hχ
  obtain ⟨y, hy, hm⟩ := exists_nonisotropic_of_span E hspan ψ hψ
  intro hz
  have hxy := mul_mem hx hy
  rw [hz, Submodule.mem_bot] at hxy
  have hp : norm (mul x y) ≠ 0 := by rw [norm_mul]; exact mul_ne_zero hn hm
  apply hp
  rw [hxy]
  rfl

/-- All occurring characters have the same multiplicity as the identity
character. Full occurrence remains a separate duality argument. -/
theorem finrank_eq_identity_of_span (E : Subgroup G)
    (hspan : (⨆ χ : Character E, characterSpace E χ) = ⊤)
    (χ : Character E) (hne : characterSpace E χ ≠ ⊥) :
    Module.finrank (ZMod 3) (characterSpace E χ) =
      Module.finrank (ZMod 3) (characterSpace E 1) := by
  obtain ⟨v, hv, hn⟩ := exists_nonisotropic_of_span E hspan χ hne
  have h := (finrank_mul (E := E) (χ := χ) v hv hn (1 : Character E)).symm
  rw [_root_.one_mul χ] at h
  exact h

/-- The characters that occur in a spanning decomposition separate the
actual subgroup elements. This uses faithfulness of the octonion action. -/
theorem eq_one_of_characters (E : Subgroup G)
    (hspan : (⨆ χ : Character E, characterSpace E χ) = ⊤)
    (g : E) (hg : ∀ χ : Character E, characterSpace E χ ≠ ⊥ → χ g = 1) : g = 1 := by
  have hfix : ∀ x : V, g.val.val x = x := by
    intro x
    have hx : x ∈ ⨆ χ : Character E, characterSpace E χ := by rw [hspan]; trivial
    refine Submodule.iSup_induction _ (motive := fun y => g.val.val y = y) hx ?_ ?_ ?_
    · intro χ y hy
      by_cases hz : characterSpace E χ = ⊥
      · have hy0 : y = 0 := by simpa only [hz, Submodule.mem_bot] using hy
        subst y; exact map_zero _
      · rw [hy g, hg χ hz]
        simp
    · exact map_zero _
    · intro y z hy hz
      rw [map_add, hy, hz]
  apply Subtype.ext
  apply Subtype.ext
  exact LinearEquiv.ext hfix

end Atlas.G2.TernaryLocals.CharacterGeometry
