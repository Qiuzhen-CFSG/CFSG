/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetStabilizer

/-!
# SextetSplitExtension

The sextet stabilizer is a split extension of the additive hexacode by its monomial
automorphisms. The affine equivalence supplies the translation inclusion, section,
quotient, and conjugation law; restricting the coordinate kernel gives its order 192.

Source: `Atlas/Mathieu/SextetSplitExtension.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def sextetTranslation : Multiplicative hexacode →* SextetStabilizer :=
  sextetAffineEquiv.toMonoidHom.comp SemidirectProduct.inl

def sextetSection : HexAutomorphisms →* SextetStabilizer :=
  sextetAffineEquiv.toMonoidHom.comp SemidirectProduct.inr

noncomputable def sextetQuotient : SextetStabilizer →* HexAutomorphisms :=
  SemidirectProduct.rightHom.comp sextetAffineEquiv.symm.toMonoidHom

@[simp] theorem sextetQuotient_affine (x : SextetAffineGroup) :
    sextetQuotient (sextetAffineEquiv x) = x.right := by
  change (sextetAffineEquiv.symm (sextetAffineEquiv x)).right = x.right
  rw [sextetAffineEquiv.symm_apply_apply]

@[simp] theorem sextetQuotient_section (g : HexAutomorphisms) :
    sextetQuotient (sextetSection g) = g := sextetQuotient_affine _

@[simp] theorem sextetQuotient_translation (t : Multiplicative hexacode) :
    sextetQuotient (sextetTranslation t) = 1 := sextetQuotient_affine _

theorem sextet_section_splits : sextetQuotient.comp sextetSection = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  exact sextetQuotient_section g

theorem sextetQuotient_surjective : Function.Surjective sextetQuotient :=
  fun g => ⟨sextetSection g,sextetQuotient_section g⟩

theorem sextetTranslation_injective : Function.Injective sextetTranslation :=
  sextetAffineEquiv.injective.comp SemidirectProduct.inl_injective

theorem sextetTranslation_coordinates (t : Multiplicative hexacode) (i : HexIndex) (k : Fin 4) :
    (sextetTranslation t).val.val (i,k) = (i,rowLabel.symm (rowLabel k+t.toAdd.val i)) := rfl

theorem sextetSection_coordinates (g : HexAutomorphisms) (i : HexIndex) (k : Fin 4) :
    (sextetSection g).val.val (i,k) =
      (g.val.perm i,rowLabel.symm (g.val.localMap (g.val.perm i) (rowLabel k))) := by
  change (g.val.perm i,rowLabel.symm (g.val.localMap (g.val.perm i) (rowLabel k) + 0)) = _
  rw [add_zero]

theorem sextet_translation_conjugation (g : HexAutomorphisms) (t : Multiplicative hexacode) :
    sextetSection g * sextetTranslation t * (sextetSection g)⁻¹ =
      sextetTranslation (hexAffineAction g t) := by
  have h := congrArg sextetAffineEquiv (SemidirectProduct.inl_aut (φ := hexAffineAction) g t)
  simp only [map_mul,map_inv] at h
  exact h.symm

theorem sextetQuotient_kernel : sextetQuotient.ker = sextetTranslation.range := by
  ext s
  constructor
  · intro hs
    refine ⟨(sextetAffineEquiv.symm s).left,?_⟩
    change sextetAffineEquiv (SemidirectProduct.inl (sextetAffineEquiv.symm s).left) = s
    apply sextetAffineEquiv.symm.injective
    rw [sextetAffineEquiv.symm_apply_apply]
    apply SemidirectProduct.ext
    · rfl
    · exact hs.symm
  · rintro ⟨t,rfl⟩
    exact sextetQuotient_translation t

theorem sextetQuotient_kernel_card : Nat.card sextetQuotient.ker = 64 := by
  rw [sextetQuotient_kernel]
  calc
    Nat.card sextetTranslation.range = Nat.card (Multiplicative hexacode) :=
      (Nat.card_congr (Equiv.ofInjective sextetTranslation sextetTranslation_injective)).symm
    _ = 64 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode ≃ hexacode),hexacode_card]

noncomputable def sextetCoordinateHom : SextetStabilizer →* Equiv.Perm (Fin 6) :=
  hexCoordinateSixHom.comp sextetQuotient

def hexKernelAffineAction : Subgroup.zpowers hexZ →* MulAut (Multiplicative hexacode) :=
  hexAffineAction.comp (Subgroup.zpowers hexZ).subtype

abbrev SextetColumnKernelAffine := Multiplicative hexacode ⋊[hexKernelAffineAction] Subgroup.zpowers hexZ

def columnKernelInclusion : SextetColumnKernelAffine →* SextetAffineGroup where
  toFun x := ⟨x.left,x.right.val⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def columnKernelHom : SextetColumnKernelAffine →* sextetCoordinateHom.ker where
  toFun x := ⟨sextetAffineEquiv (columnKernelInclusion x),by
    change hexCoordinateSixHom (sextetQuotient (sextetAffineEquiv (columnKernelInclusion x))) = 1
    rw [sextetQuotient_affine]
    change x.right.val ∈ hexCoordinateSixHom.ker
    rw [hexCoordinateSix_kernel]
    exact x.right.prop⟩
  map_one' := by apply Subtype.ext; exact map_one (sextetAffineEquiv.toMonoidHom.comp columnKernelInclusion)
  map_mul' _ _ := by apply Subtype.ext; exact map_mul (sextetAffineEquiv.toMonoidHom.comp columnKernelInclusion) _ _

theorem columnKernelHom_bijective : Function.Bijective columnKernelHom := by
  constructor
  · intro x y h
    have hh := sextetAffineEquiv.injective (congrArg Subtype.val h)
    exact SemidirectProduct.ext (congrArg (fun a : SextetAffineGroup => a.left) hh)
      (Subtype.ext (congrArg (fun a : SextetAffineGroup => a.right) hh))
  · intro s
    let x := sextetAffineEquiv.symm s.val
    have hx : x.right ∈ Subgroup.zpowers hexZ := by
      rw [← hexCoordinateSix_kernel]
      exact s.prop
    refine ⟨⟨x.left,⟨x.right,hx⟩⟩,?_⟩
    apply Subtype.ext
    exact sextetAffineEquiv.apply_symm_apply s.val

noncomputable def sextetColumnKernelEquiv : SextetColumnKernelAffine ≃* sextetCoordinateHom.ker :=
  MulEquiv.ofBijective columnKernelHom columnKernelHom_bijective

theorem sextetCoordinate_kernel_card : Nat.card sextetCoordinateHom.ker = 192 := by
  rw [Nat.card_congr sextetColumnKernelEquiv.symm.toEquiv,SemidirectProduct.card,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode ≃ hexacode),
    hexacode_card,Nat.card_zpowers,hexZ_order]

end Atlas.Codes
