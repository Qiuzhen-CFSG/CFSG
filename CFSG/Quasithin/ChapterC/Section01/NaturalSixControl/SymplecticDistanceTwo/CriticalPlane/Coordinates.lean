module
public import Theory.Representation.BinaryOffender.FourSpaceFixedDisplacement
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeLayer
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Displacement of the fixed part of the native moving layer

An intermediate elementary image with only the edge line fixed acts
quadratically on the fixed space of any nontrivial smaller actor. The
literal natural coordinates transport this to [B,C_W(A)] ≤ Ω₁Z(R).
The critical-plane consumer supplies the fixed-line premise from the
proved critical intersection. Source: MS93 (3.6), printed p.871.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

theorem module_fixed_commutator_le_seed (A B : Subgroup M)
    (hAB : A ≤ B) (hBR : B ≤ R) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hne : ¬ A ≤ pCore 2 M)
    (hfix : W ⊓ centralizer (B : Set M) ≤ omegaCenter R) :
    ⁅B,W ⊓ centralizer (A : Set M)⁆ ≤ omegaCenter R := by
  let := s.module_elementary
  let d : NaturalAction W := ⟨s.projection,
    s.projection_surjective_of_radical_image_le_conjugate t (by
      rw [Model.pointCore_eq_exceptional] at hfull; exact hfull.le),
    s.projection_kernel,s.coordinates,s.action⟩
  have he : W ⊓ centralizer (B : Set M) = W ⊓ omegaCenter R := by
    apply le_antisymm (le_inf inf_le_left hfix)
    rw [s.module_inf_seed_eq_fixed]
    exact inf_le_inf_left _ (centralizer_le hBR)
  have hfixed : Module.finrank (ZMod 2) (fixedSpace Model.rho (B.map s.projection)) = 1 := by
    have hh := d.fixed_card B
    rw [he,s.module_inf_seed_card t hfull] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  have hBi : B.map s.projection ≤ pointCore.map (MulAut.conj t).toMonoidHom :=
    (map_mono hBR).trans_eq hfull
  let := pointCore_elementary
  let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj t).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (B.map s.projection) :=
    IsElementaryAbelian.of_injective (inclusion hBi) (inclusion_injective hBi)
  have hAi : A.map s.projection ≠ ⊥ := by
    intro hh
    apply hne
    rw [←s.projection_kernel]
    exact (map_eq_bot_iff A).mp hh
  have hdisp := displacement_fixed_of_proper_fixedSpace Model.rho
    (naturalRepresentation_injective (Fin 6) (by decide))
    (by exact finrank_natural_even (Fin 6) (by decide)) (map_mono hAB) hAi hfixed
  apply commutator_le.mpr
  intro b hb w hw
  let w0 : W := ⟨w,hw.1⟩
  have hwf : (s.coordinates w0).toAdd ∈ fixedSpace Model.rho (A.map s.projection) := by
    rintro ⟨_,⟨a,ha,rfl⟩⟩
    have he : MulAut.conjNormal a w0 = w0 := by
      apply Subtype.ext
      change a*w*a⁻¹=w
      rw [hw.2 a ha,mul_inv_cancel_right]
    exact (s.action a w0).symm.trans (congrArg (fun x : W => (s.coordinates x).toAdd) he)
  let v : W := MulAut.conjNormal b w0 * w0⁻¹
  have hv : (s.coordinates v).toAdd =
      Model.rho (s.projection b) (s.coordinates w0).toAdd - (s.coordinates w0).toAdd := by
    dsimp only [v]
    rw [map_mul,map_inv]
    change (s.coordinates (MulAut.conjNormal b w0)).toAdd + -(s.coordinates w0).toAdd = _
    rw [s.action]
    exact (sub_eq_add_neg _ _).symm
  have hvc : (v : M) ∈ centralizer (B : Set M) := by
    intro z hz
    have he : MulAut.conjNormal z v = v := by
      apply s.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [s.action,hv]
      exact (hdisp (s.projection b) (mem_map_of_mem _ hb) _ hwf)
        ⟨s.projection z,mem_map_of_mem _ hz⟩
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  exact hfix ⟨v.property,hvc⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
