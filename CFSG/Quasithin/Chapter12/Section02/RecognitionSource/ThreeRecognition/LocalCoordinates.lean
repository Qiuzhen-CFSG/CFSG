module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition.LocalCore
public import Theory.SpecificGroups.BinaryLinear.AffineThree.Coordinates

/-!
# Choosing a standard marked point in the original affine group

The original split equivalence chooses a nonidentity element of V mapping to
the first coordinate translation. No escape then identifies its full ambient
centralizer with the computed affine centralizer, preserving that element.
This supplies the actual source consumer of the explicit affine coordinates.

Source: Aschbacher–Smith 12.2.26–27, printed pp.806–807.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.SplitLinearConfiguration
open BinaryLinear.Affine.ThreeLocal
variable {G : Type*} [Group G]
variable {L V : Subgroup G}

theorem exists_standard_point_centralizer (C : SplitLinearConfiguration L V 3)
    (hnone : NoEscape L V) :
    ∃ v : G, v ∈ V ∧ v ≠ 1 ∧
      ∃ E : centralizer ({v} : Set G) ≃* H,
        (E ⟨v, mem_centralizer_singleton_iff.mpr rfl⟩ : BinaryLinear.Affine.Model 3) =
          SemidirectProduct.inl e0 := by
  obtain ⟨f,e,he⟩ := C.exists_affine_equiv
  let vV := f.symm e0
  let v : G := vV
  have hv : v ∈ V := vV.property
  have he0 : e0 ≠ 1 := by
    intro hh
    have ht := congrArg (fun w : Multiplicative (Fin 3 → ZMod 2) => w.toAdd 0) hh
    change (1 : ZMod 2) = 0 at ht
    exact one_ne_zero ht
  have hv1 : v ≠ 1 := by
    intro hh
    apply he0
    have hvV : vV = 1 := Subtype.ext hh
    have hff : f vV = e0 := f.apply_symm_apply e0
    rw [hvV, map_one] at hff
    exact hff.symm
  let u := C.coreEquiv.symm vV
  have hu : (((u : pCore 2 L) : L) : G) = v :=
    (C.coreEquiv_apply u).symm.trans (congrArg Subtype.val (C.coreEquiv.apply_symm_apply vV))
  let vL : L := u
  have hvL : (vL : G) = v := hu
  have hCL : centralizer ({v} : Set G) ≤ L := by
    rw [C.point_centralizer_eq hnone hv hv1]
    exact inf_le_left
  have hlocal : (centralizer ({v} : Set G)).subgroupOf L =
      centralizer ({vL} : Set L) := by
    ext x
    simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro hh
      apply Subtype.ext
      simpa only [coe_mul, hvL] using hh
    · intro hh
      simpa only [coe_mul, hvL] using congrArg Subtype.val hh
  let E := (subgroupOfEquivOfLe hCL).symm.trans
    ((MulEquiv.subgroupCongr hlocal).trans
      (((centralizer ({vL} : Set L)).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (CentralizerSmallKernelTransport.map_centralizer e vL))))
  have hev : e vL = SemidirectProduct.inl e0 := by
    rw [show vL = (u : L) from rfl, he]
    simp only [u, C.coreEquiv.apply_symm_apply, vV, f.apply_symm_apply]
  let F := E.trans (MulEquiv.subgroupCongr
    (congrArg (fun a : BinaryLinear.Affine.Model 3 => centralizer ({a} : Set (BinaryLinear.Affine.Model 3))) hev))
  refine ⟨v,hv,hv1,F,?_⟩
  change e ⟨v,hCL (mem_centralizer_singleton_iff.mpr rfl)⟩ = _
  exact (congrArg e (Subtype.ext hvL.symm)).trans hev

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.SplitLinearConfiguration
