module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Source
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.MovingFixer
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Critical-image control in the original natural coordinates

A subgroup centralizing [W,A] fixes the literal displacement space of the
image of A under the specified source projection. The quadratic point-core
fixer calculation then gives image order two when that centralizer has a
strictly larger image. No surjectivity of the source projection is needed.

Source: MS93 (3.3)(ii), (3.6), printed pp.867,871.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem image_fixes_moved_of_centralizes (A Y : Subgroup M)
    (hY : Y ≤ centralizer ((⁅W,A⁆ : Subgroup M) : Set M)) :
    Y.map s.projection ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection)) ⊤ := by
  rintro _ ⟨y,hy,rfl⟩
  refine ⟨mem_top _,?_⟩
  have hspace : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection) ≤
      LinearMap.ker (naturalRepresentation (Fin 6) (s.projection y) - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,_,rfl⟩
    let w := s.coordinates.symm (Multiplicative.ofAdd v)
    let d : W := MulAut.conjNormal a w * w⁻¹
    have hd : (d : M) ∈ ⁅W,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha w.property
    have he : MulAut.conjNormal y d = d := by
      apply Subtype.ext
      change y*(d:M)*y⁻¹=(d:M)
      rw [←hY hy (d:M) hd,mul_inv_cancel_right]
    have hcoords : (s.coordinates d).toAdd =
        naturalRepresentation (Fin 6) (s.projection a) v-v := by
      change (s.coordinates (MulAut.conjNormal a w * w⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      change (s.coordinates (MulAut.conjNormal a w)).toAdd + -(s.coordinates w).toAdd = _
      rw [s.action]
      have hw : (s.coordinates w).toAdd=v := by dsimp [w];rw [MulEquiv.apply_symm_apply];rfl
      rw [hw,sub_eq_add_neg]
    have hfixed := s.action y d
    rw [he] at hfixed
    change naturalRepresentation (Fin 6) (s.projection y)
      (naturalRepresentation (Fin 6) (s.projection a) v-v) -
      (naturalRepresentation (Fin 6) (s.projection a) v-v)=0
    rw [←hcoords,←hfixed,sub_self]
  intro v hv
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hspace hv

theorem image_card_two_of_centralizes_moved (A Y : Subgroup M) (t : S)
    (hAY : A ≤ Y)
    (hY : Y.map s.projection ≤ pointCore.map (MulAut.conj t).toMonoidHom)
    (hcentral : Y ≤ centralizer ((⁅W,A⁆ : Subgroup M) : Set M))
    (hne : ¬ A ≤ pCore 2 M) (hproper : ¬ Y ≤ A ⊔ pCore 2 M) :
    Nat.card (A.map s.projection) = 2 := by
  apply QuadraticPointCore.card_two_of_centralizes_moved
    (A.map s.projection) (Y.map s.projection) t (map_mono hAY) hY
    (s.image_fixes_moved_of_centralizes A Y hcentral)
  · intro hbot
    apply hne
    rw [←s.projection_kernel]
    exact (Subgroup.map_eq_bot_iff A).mp hbot
  · intro hle
    apply hproper
    simpa only [s.projection_kernel] using (map_le_map_iff.mp hle)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
