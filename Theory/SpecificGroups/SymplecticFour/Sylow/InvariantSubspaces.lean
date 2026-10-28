module
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Natural
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The standard symplectic Sylow flag and its local overgroups

The established invariant line and plane theorem for the derived Sylow
applies to the full unipotent Sylow. The radical of the fixed space of a
nontrivial normal two-subgroup is a nonzero invariant isotropic subspace;
it must therefore be the standard point or plane. Consequently a
characteristic-two overgroup of the standard Sylow lies in one of the two
standard parabolics. No coverage claim for arbitrary overgroups is used.

Source: Aschbacher--Smith 2.5.2(2), printed p.551; the fixed-space geometry
of the concrete symplectic model.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem unipotent_invariant_line_unique (W : Submodule F (Vector F))
    (hW : unipotent ≤ stabilizer W) (hdim : Module.finrank F W = 1) : W = point F := by
  have he := SylowFlag.invariant_line_unique (K := F) W (fun g x hx =>
    (mem_stabilizer_iff W g.val.val).mp (hW g.property) x hx) hdim
  exact he.trans SylowFlag.firstLine_eq_point

theorem unipotent_invariant_plane_unique (W : Submodule F (Vector F))
    (hW : unipotent ≤ stabilizer W) (hdim : Module.finrank F W = 2) : W = plane F := by
  have he := SylowFlag.invariant_plane_unique (K := F) W (fun g x hx =>
    (mem_stabilizer_iff W g.val.val).mp (hW g.property) x hx) hdim
  exact he.trans SylowFlag.secondPlane_eq_plane

theorem unipotent_overgroup_parabolic_of_normal_twoGroup
    (J Q : Subgroup (Sp F)) (hUJ : unipotent ≤ J)
    (hQ : Q ≠ ⊥) (hp : IsPGroup 2 Q) (hn : J ≤ normalizer (Q : Set (Sp F))) :
    J ≤ pointParabolic ∨ J ≤ planeParabolic := by
  let W := TwoLocalCover.fixedRadical Q
  have hw : W ≠ ⊥ := TwoLocalCover.fixedRadical_ne_bot Q hQ hp
  have hd : Module.finrank F W ≤ 2 :=
    TwoLocalCover.finrank_le_two_of_isotropic W (fun x hx y hy =>
      TwoLocalCover.fixedRadical_isotropic Q x y hx hy)
  have hJW : J ≤ stabilizer W := hn.trans (TwoLocalCover.normalizer_le_fixedRadical_stabilizer Q)
  have hd0 : Module.finrank F W ≠ 0 := by
    intro he
    exact hw (Submodule.finrank_eq_zero.mp he)
  have hor : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
  rcases hor with hd | hd
  · left
    rw [unipotent_invariant_line_unique W (hUJ.trans hJW) hd] at hJW
    exact hJW
  · right
    rw [unipotent_invariant_plane_unique W (hUJ.trans hJW) hd] at hJW
    exact hJW

theorem unipotent_overgroup_parabolic_of_characteristicTwo
    (J : Subgroup (Sp F)) (hUJ : unipotent ≤ J) (hJ : J ≠ ⊥)
    (hc : centralizer (pCore 2 J : Set J) ≤ pCore 2 J) :
    J ≤ pointParabolic ∨ J ≤ planeParabolic := by
  have hne : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hJ
    apply bot_unique
    intro x hx
    have hh := (inf_centralizer_pCoreIn_le_iff 2 J).mpr hc
    rw [he] at hh
    apply hh
    refine ⟨hx, ?_⟩
    intro y hy
    rw [show y = 1 from hy]
    simp
  exact unipotent_overgroup_parabolic_of_normal_twoGroup J (J.pCoreIn 2) hUJ hne
    (isPGroup_pCoreIn 2 J)
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
end Theory.SpecificGroups.SymplecticFour
