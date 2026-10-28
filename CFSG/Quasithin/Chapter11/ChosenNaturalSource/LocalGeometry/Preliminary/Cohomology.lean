module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.Representation.G2OrthogonalCover.Universal
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Dual cohomology for the full natural markings in 11.0.3

Inverse transpose and the dot product followed by a nonzero binary functional
identify the binary dual natural SL₃ action with the graph twist of its natural
action. Thus the checked natural cohomology vanishes when the field is nonbinary.
For Sp₄ and G₂ the checked derived-group cover calculations apply to the full
markings because their actual source quotients are perfect.

Source: Aschbacher--Smith, I.1.6, printed p.408, used in 11.0.3(3), p.760.
-/

@[expose] public noncomputable section
open Representation Representation.OneCohomology Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
namespace LinearThree
variable (F : BinaryField)
private abbrev Actor := SpecialLinearGroup (Fin 3) F.Carrier
private abbrev Space := Fin 3 → F.Carrier

private lemma transpose_mul (g h : Actor F) : (g * h).transpose = h.transpose * g.transpose := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _
private lemma transpose_inv (g : Actor F) : g⁻¹.transpose = g.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel]
  apply Subtype.ext
  exact Matrix.transpose_one
private def graph : MulAut (Actor F) where
  toFun g := g⁻¹.transpose
  invFun g := g⁻¹.transpose
  left_inv g := by
    change (g⁻¹.transpose)⁻¹.transpose = g
    rw [transpose_inv]
    change (g⁻¹)⁻¹ = g
    exact inv_inv g
  right_inv g := by
    change (g⁻¹.transpose)⁻¹.transpose = g
    rw [transpose_inv]
    change (g⁻¹)⁻¹ = g
    exact inv_inv g
  map_mul' g h := by rw [_root_.mul_inv_rev, transpose_mul]

private def coefficient : F.Carrier →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (Module.Projective.exists_dual_eq_one (ZMod 2)
    (one_ne_zero : (1 : F.Carrier) ≠ 0))
private lemma coefficient_one : coefficient F 1 = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one (ZMod 2)
    (one_ne_zero : (1 : F.Carrier) ≠ 0))

private def pairing : Space F →ₗ[ZMod 2] Module.Dual (ZMod 2) (Space F) where
  toFun v := (coefficient F).comp ((dotProductEquiv F.Carrier (Fin 3) v).restrictScalars (ZMod 2))
  map_add' v w := by ext x; simp [map_add]
  map_smul' a v := by ext x; simp [map_smul]

private lemma pairing_injective : Function.Injective (pairing F) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  change v = 0
  ext i
  by_contra hi
  have h := LinearMap.congr_fun hv (Pi.single i (v i)⁻¹)
  change coefficient F (v ⬝ᵥ Pi.single i (v i)⁻¹) = 0 at h
  rw [dotProduct_single, mul_inv_cancel₀ hi, coefficient_one] at h
  exact one_ne_zero h

private def dualEquiv : Space F ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Space F) :=
  LinearEquiv.ofBijective (pairing F) ⟨pairing_injective F,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp (pairing_injective F)⟩

private lemma dualEquiv_intertwines (g : Actor F) (v : Space F) :
    dualEquiv F (linearNatural F 3 (graph F g) v) =
      (linearNatural F 3).dual g (dualEquiv F v) := by
  apply LinearMap.ext
  intro w
  change coefficient F (((g⁻¹.val)ᵀ *ᵥ v) ⬝ᵥ w) =
    coefficient F (v ⬝ᵥ (g⁻¹.val *ᵥ w))
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.transpose_transpose]

/-- Binary dual cohomology vanishes for the full nonbinary SL₃ natural action. -/
theorem dual_H1_finrank (hn : 1 < F.degree) :
    Module.finrank (ZMod 2) (H1 (linearNatural F 3).dual) = 0 := by
  have he : ∀ g v, dualEquiv F (linearNatural F 3 g v) =
      (linearNatural F 3).dual ((graph F).symm g) (dualEquiv F v) := by
    intro g v
    simpa only [MulEquiv.apply_symm_apply] using dualEquiv_intertwines F ((graph F).symm g) v
  have hd := (H1Congr (linearNatural F 3) (linearNatural F 3).dual
    (graph F).symm (dualEquiv F) he).finrank_eq
  rw [← hd]
  exact SLHigherNatural.finrank_restrict_sl3_of_card_pow F.degree F.card_eq |>.trans
    (if_neg (by omega))
end LinearThree

/-- Passing from a perfect full group to its literal derived subgroup changes no cohomology. -/
theorem dual_cohomology_eq_derived
    {A W : Type*} [Group A] [Group.IsPerfect A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) :
    Module.finrank (ZMod 2) (H1 ρ.dual) =
      Module.finrank (ZMod 2) (H1 (Representation.dual (ρ.comp (commutator A).subtype))) := by
  let e : commutator A ≃* A := MulEquiv.ofBijective (commutator A).subtype
    ⟨Subtype.val_injective, fun a => ⟨⟨a, Group.IsPerfect.mem_commutator⟩, rfl⟩⟩
  exact (H1Congr (Representation.dual (ρ.comp (commutator A).subtype)) ρ.dual e
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl)).finrank_eq.symm
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
