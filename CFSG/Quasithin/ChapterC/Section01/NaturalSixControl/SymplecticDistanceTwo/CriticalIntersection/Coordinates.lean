module
public import Theory.Representation.BinaryOffender.SmallFixedCodimension
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeLayer

/-!
# Extra fixed vectors force quadratic action on the native moving layer

The full point core fixes a line. If an intermediate edge subgroup fixes
an additional vector, its fixed codimension on the natural four-space is
at most two, so the action is quadratic. The literal conjugation coordinates
then place the group commutator in the actual centralizer.

Source: MS93 (3.6), printed p.871. The critical-intersection consumer
constructs the extra fixed vector from Zc=Uc Zb.
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

omit [Finite M] in
private theorem module_commutator_le_centralizer_of_quadratic (Y : Subgroup M)
    (hq : IsQuadratic Model.rho (Y.map s.projection)) :
    ⁅W,Y⁆ ≤ centralizer (Y : Set M) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro y hy w hw
  let w0 : W := ⟨w,hw⟩
  let v : W := MulAut.conjNormal y w0 * w0⁻¹
  have hv : (s.coordinates v).toAdd =
      Model.rho (s.projection y) (s.coordinates w0).toAdd - (s.coordinates w0).toAdd := by
    dsimp only [v]
    rw [map_mul,map_inv]
    change (s.coordinates (MulAut.conjNormal y w0)).toAdd + -(s.coordinates w0).toAdd = _
    rw [s.action]
    exact (sub_eq_add_neg _ _).symm
  intro z hz
  have he : MulAut.conjNormal z v = v := by
    apply s.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [s.action,hv,hq _ (mem_map_of_mem _ hz) _ (mem_map_of_mem _ hy)]
  have hh := congrArg Subtype.val he
  change z * ⁅y,w⁆ * z⁻¹ = ⁅y,w⁆ at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

theorem module_commutator_le_centralizer_of_fixed_escape (Y : Subgroup M) (hY : Y ≤ R)
    (t : S) (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hescape : ¬ W ⊓ centralizer (Y : Set M) ≤ omegaCenter R) :
    ⁅W,Y⁆ ≤ centralizer (Y : Set M) := by
  let := s.module_elementary
  let d : NaturalAction W := ⟨s.projection,
    s.projection_surjective_of_radical_image_le_conjugate t (by
      rw [Model.pointCore_eq_exceptional] at hfull
      exact hfull.le),
    s.projection_kernel,s.coordinates,s.action⟩
  have hFC : W ⊓ omegaCenter R ≤ W ⊓ centralizer (Y : Set M) := by
    rw [s.module_inf_seed_eq_fixed]
    exact inf_le_inf_left _ (centralizer_le hY)
  have hdim : 2 ≤ Module.finrank (ZMod 2) (fixedSpace Model.rho (Y.map s.projection)) := by
    by_contra! hh
    have hcard : Nat.card (W ⊓ centralizer (Y : Set M) : Subgroup M) ≤ 2 := by
      rw [d.fixed_card]
      change 2 ^ Module.finrank (ZMod 2) (fixedSpace Model.rho (Y.map s.projection)) ≤ 2
      have hle : Module.finrank (ZMod 2) (fixedSpace Model.rho (Y.map s.projection)) ≤ 1 := by omega
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) hle).trans (by norm_num)
    have he : W ⊓ omegaCenter R = W ⊓ centralizer (Y : Set M) :=
      eq_of_le_of_card_ge hFC ((s.module_inf_seed_card t hfull).symm ▸ hcard)
    apply hescape
    rw [←he]
    exact inf_le_right
  have hcodim : fixedCodim Model.rho (Y.map s.projection) ≤ 2 := by
    have hh := fixedCodim_add_finrank Model.rho (Y.map s.projection)
    rw [finrank_natural_even (Fin 6) (by decide)] at hh
    change _ + _ = 4 at hh
    omega
  have hYC : Y.map s.projection ≤ pointCore.map (MulAut.conj t).toMonoidHom :=
    (map_mono hY).trans_eq hfull
  let := pointCore_elementary
  let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj t).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (Y.map s.projection) :=
    IsElementaryAbelian.of_injective (inclusion hYC) (inclusion_injective hYC)
  exact s.module_commutator_le_centralizer_of_quadratic Y
    (isQuadratic_of_fixedCodim_le_two Model.rho hcodim)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
