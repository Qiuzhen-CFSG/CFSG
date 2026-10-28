module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Displacement in repeated and natural-plus-dual source actions

The image of a coordinatewise map is the product of its images. Repetition
therefore multiplies displacement rank by the multiplicity. Contragredience
preserves the displacement of an individual actor, so a natural-plus-dual
action has even displacement. The original rank-one actor in G.6.4 consequently
rules out the doubled and natural-plus-dual B.5.1 rows.

Source: Aschbacher–Smith, B.5.1(1), p.99, and G.6.4, p.346.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D E V W : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}

theorem ActionEquiv.displacement_rank (e : ActionEquiv ρ σ) (a : D) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (σ (e.groupEquiv a) - LinearMap.id)) := by
  have he := fixedCodim_map_equivariant ρ σ e.groupEquiv.toMonoidHom
    e.linearEquiv e.intertwines (zpowers a)
  simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    fixedCodim_zpowers_eq_displacement_rank] using he

theorem repeated_displacement_rank (ρ : Representation (ZMod 2) D V) (r : ℕ) (a : D) :
    Module.finrank (ZMod 2) (LinearMap.range (repeated ρ r a - LinearMap.id)) =
      r * Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) := by
  let δ := ρ a - LinearMap.id
  have he : repeated ρ r a - LinearMap.id = δ.compLeft (Fin r) := rfl
  rw [he, LinearMap.range_compLeft]
  let e : Submodule.pi Set.univ (fun _ : Fin r => LinearMap.range δ) ≃ₗ[ZMod 2]
      (Fin r → LinearMap.range δ) :=
    { toFun := fun v i => ⟨v.val i, v.property i trivial⟩
      invFun := fun v => ⟨fun i => (v i).val, fun i _ => (v i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] using e.finrank_eq

theorem naturalPlusDual_displacement_rank (d : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin d) BinaryField.two.Carrier) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalPlusDual d a - LinearMap.id)) =
      2 * Module.finrank (ZMod 2)
        (LinearMap.range (linearNatural BinaryField.two d a - LinearMap.id)) := by
  rw [← fixedCodim_zpowers_eq_displacement_rank]
  change fixedCodim ((linearNatural BinaryField.two d).prod
    (linearNatural BinaryField.two d).dual) (zpowers a) = _
  rw [fixedCodim_prod, fixedCodim_zpowers_dual, fixedCodim_zpowers_eq_displacement_rank,
    two_mul]
end CFSG.Quasithin.ChapterB.QuasisimpleSource
