module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.PointRestriction.SimpleDegrees

/-!
# A binary degree gap for PSL₃(4)

The existing tensor-word classification gives degree one or nine for each
simple binary module of dimension at most twelve. A binary line has trivial
action, so every nontrivial simple action has degree at least nine. Field
transport retains arbitrary four-element coordinates and any supplied group
marking. The faithful form supplies the degree obstruction for disjoint
constituents in the PSL₃(4) chief-factor argument.

Source: GLS III §§2.8.6, 2.8.8 and 2.8.10(c), via the proved classification in
`Mathieu.SmallModules.M22Recognition.PointRestriction.SimpleDegrees`.
-/

public noncomputable section
open Representation
open scoped MatrixGroups
namespace Representation.PSL3Four

private theorem binary_line_action {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (τ : Representation (ZMod 2) G W)
    (hd : Module.finrank (ZMod 2) W = 1) (g : G) : τ g = 1 := by
  ext w
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hw (τ g w)
  have hc0 : c ≠ 0 := by
    intro hz
    have hgw : τ g w = 0 := by simpa [hz] using hc.symm
    apply hw
    simpa only [τ.inv_self_apply, map_zero] using congrArg (τ g⁻¹) hgw
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa only [hc1, one_smul, Module.End.one_apply] using hc.symm

private def coefficientEquiv {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) : F ≃+* Matrix.PSL3Four.F := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      Matrix.PSL3Four.card_F])

variable {F G W : Type*} [Field F] [Finite F] [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The degree of a nontrivial binary simple PSL₃(4) module is at least nine. -/
theorem finrank_ge_nine (hF : Nat.card F = 4)
    (τ : Representation (ZMod 2) PSL(3,F) W) [τ.IsIrreducible]
    (hτ : ∃ g, τ g ≠ 1) : 9 ≤ Module.finrank (ZMod 2) W := by
  by_contra! hd
  let e := Atlas.fieldEquivPSL 3 (coefficientEquiv hF)
  let τ' : Representation (ZMod 2) Matrix.PSL3Four.PSL W := τ.comp e.symm.toMonoidHom
  let : τ'.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  have hs := MathieuSmall.M22Recognition.PointRestriction.SimpleDegrees.simple_degree τ'
    (by omega)
  have hline : Module.finrank (ZMod 2) W = 1 := by omega
  obtain ⟨g, hg⟩ := hτ
  exact hg (binary_line_action τ hline g)

/-- The degree bound keeps the supplied projective marking and the original action. -/
theorem finrank_ge_nine_of_equiv (hF : Nat.card F = 4) (e : G ≃* PSL(3,F))
    (τ : Representation (ZMod 2) G W) [τ.IsIrreducible]
    (hτ : ∃ g, τ g ≠ 1) : 9 ≤ Module.finrank (ZMod 2) W := by
  let σ : Representation (ZMod 2) PSL(3,F) W := τ.comp e.symm.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  apply finrank_ge_nine hF σ
  obtain ⟨g, hg⟩ := hτ
  exact ⟨e g, by simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using hg⟩

/-- A faithful binary simple action of any marked PSL₃(4) has degree greater than four. -/
theorem finrank_gt_four_of_faithful (hF : Nat.card F = 4) (e : G ≃* PSL(3,F))
    (τ : Representation (ZMod 2) G W) (hf : Function.Injective τ)
    (hi : τ.IsIrreducible) : 4 < Module.finrank (ZMod 2) W := by
  let : τ.IsIrreducible := hi
  let e' := e.trans (Atlas.fieldEquivPSL 3 (coefficientEquiv hF))
  let : Finite G := Finite.of_equiv Matrix.PSL3Four.PSL e'.toEquiv.symm
  have hcard : Nat.card G = 20160 :=
    (Nat.card_congr e'.toEquiv).trans Matrix.PSL3Four.card_PSL
  let : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hd := finrank_ge_nine_of_equiv hF e τ ⟨g, fun h => hg (hf (h.trans τ.map_one.symm))⟩
  omega

end Representation.PSL3Four
