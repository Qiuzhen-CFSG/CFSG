module
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.Extension

/-!
# Graph transport of the scalar character

A character trivial on SL₃ factors through the actual determinant. Endomorphisms
of the cyclic multiplicative field group commute, so graph-field transport
inverts the coefficient-transported character. No choice of field bit is made.

Source motivation: Aschbacher–Smith B.4.14, printed p.98, and the nonblock
argument for original 4.3.2, pp.618–619. These are representation consequences
of explicit action hypotheses; constructing the source Frattini marking and
discharging its action-kernel descent are separate source obligations.
-/

open Matrix Representation
open scoped MatrixGroups
namespace Representation.SL3.AdjointCubicCentralizer.GraphExtension
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F]

@[simp] theorem det_diagonalHom (a : Fˣ) : GeneralLinearGroup.det (diagonalHom F a) = a := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply,diagonalHom,diagonalUnit,block,Matrix.det_fin_three]

theorem character_det (χ : GL (Fin 3) F →* Fˣ)
    (hχ : ∀ s : SL(3,F), χ (SpecialLinearGroup.toGL s) = 1)
    (g : GL (Fin 3) F) :
    χ g = χ (diagonalHom F (GeneralLinearGroup.det g)) := by
  let k := g * (diagonalHom F (GeneralLinearGroup.det g))⁻¹
  have hk : GeneralLinearGroup.det k = 1 := by simp [k]
  let s := (Matrix.PSL3.OuterSolvable.slEquivDetKernel F).symm ⟨k,hk⟩
  have hs : SpecialLinearGroup.toGL s = k :=
    Matrix.PSL3.OuterSolvable.slEquivDetKernel_symm_toGL F _
  have he := hχ s
  rw [hs] at he
  change χ (g * (diagonalHom F (GeneralLinearGroup.det g))⁻¹) = 1 at he
  simpa only [map_mul,map_inv,mul_inv_eq_one] using he

private theorem cyclic_homs_commute {C : Type*} [Group C] [IsCyclic C]
    (f g : C →* C) (x : C) : f (g x) = g (f x) := by
  obtain ⟨z,hz⟩ := exists_zpow_surjective C
  obtain ⟨i,hi⟩ := hz (f z)
  obtain ⟨j,hj⟩ := hz (g z)
  obtain ⟨k,rfl⟩ := hz x
  simp only [map_zpow,←hi,←hj,←zpow_mul]
  congr 1
  ring

def graphFieldGL (σ : F ≃+* F) : GL (Fin 3) F →* GL (Fin 3) F :=
  (Matrix.PSL3.OuterSolvable.inverseTransposeGL F).comp
    (GeneralLinearGroup.map σ.toRingHom)

theorem det_graphFieldGL (σ : F ≃+* F) (g : GL (Fin 3) F) :
    GeneralLinearGroup.det (graphFieldGL F σ g) =
      Units.map σ.toMonoidHom (GeneralLinearGroup.det g)⁻¹ := by
  apply Units.ext
  change Matrix.det ((GeneralLinearGroup.map σ.toRingHom g).inv.transpose) = _
  rw [Matrix.det_transpose]
  change (GeneralLinearGroup.det (GeneralLinearGroup.map σ.toRingHom g)⁻¹ : F) = _
  rw [map_inv,GeneralLinearGroup.map_det]
  rfl

theorem character_graphField [Finite F] (χ : GL (Fin 3) F →* Fˣ)
    (hχ : ∀ s : SL(3,F), χ (SpecialLinearGroup.toGL s) = 1)
    (σ : F ≃+* F) (g : GL (Fin 3) F) :
    χ (graphFieldGL F σ g) = Units.map σ.toMonoidHom (χ g)⁻¹ := by
  rw [character_det F χ hχ (graphFieldGL F σ g),det_graphFieldGL]
  let ψ := χ.comp (diagonalHom F)
  change ψ (Units.map σ.toMonoidHom (GeneralLinearGroup.det g)⁻¹) = _
  rw [cyclic_homs_commute,map_inv]
  change Units.map σ.toMonoidHom (χ (diagonalHom F (GeneralLinearGroup.det g)))⁻¹ = _
  rw [←character_det F χ hχ g]

end
end Representation.SL3.AdjointCubicCentralizer.GraphExtension
