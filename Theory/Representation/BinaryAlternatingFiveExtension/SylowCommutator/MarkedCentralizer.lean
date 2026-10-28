module
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowGraphCenter
/-!
# Marked short centralizers in the affine Sylow

The cyclic displacement line is one dihedral-factor center. Every dihedral
comparison preserves its unique nonidentity central element. Swapping the
factors when necessary therefore gives a single comparison sending the short
involution to the first factor center and the whole-Sylow central involution
to the diagonal center.

This marks the quotient calculation in Aschbacher--Smith F.5.5, pp.301--302.
-/

@[expose] public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension.SylowCommutator
open Subgroup SylowModel
open scoped commutatorElement
private instance : Fintype PlaneWreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd PlaneGroup Bit).symm
private instance : DecidableEq PlaneWreath := (RegularWreathProduct.equivProd PlaneGroup Bit).injective.decidableEq
private def planeRoot : PlaneGroup := SemidirectProduct.inl (.ofAdd 1,.ofAdd 1)
private def wreathRoot : PlaneWreath := baseMap (axis 1)*baseMap (axis (.ofAdd 1))
private theorem root_test : ∀ z : PlaneWreath,
    (∀ y : PlaneWreath,z*y=y*z) → z≠1 → z=wreathRoot := by decide +kernel
private theorem dihedral_center_test : ∀ z : DihedralGroup 4,
    (∀ y : DihedralGroup 4,z*y=y*z) → z≠1 → z=DihedralGroup.r 2 := by decide +kernel
private theorem plane_root_mark (d : PlaneGroup ≃* DihedralGroup 4) :
    d planeRoot=DihedralGroup.r 2 := by
  apply dihedral_center_test
  · intro y
    obtain ⟨x,rfl⟩ := d.surjective y
    exact (map_mul d _ _).symm.trans ((congrArg d
      ((by decide +kernel : ∀ x : PlaneGroup,planeRoot*x=x*planeRoot) x)).trans (map_mul d _ _))
  · intro hh
    have he : planeRoot=1 := d.injective (hh.trans d.map_one.symm)
    exact (by decide +kernel : planeRoot≠1) he

private theorem exists_marked_axis_centralizer (j : Bit) :
    ∃ d : centralizer ({baseMap (axis j)} : Set PlaneWreath) ≃* DihedralGroup 4 × DihedralGroup 4,
      (∀ x, x.val=baseMap (axis j) → d x=(DihedralGroup.r 2,1)) ∧
      (∀ x, x.val=wreathRoot → d x=(DihedralGroup.r 2,DihedralGroup.r 2)) := by
  obtain ⟨e⟩ := plane_dihedral
  let d := (centralizerAxisEquiv j).trans (MulEquiv.prodCongr e e)
  have hj : j=1 ∨ j=Multiplicative.ofAdd 1 :=
    (by decide : ∀ j : Bit,j=1 ∨ j=Multiplicative.ofAdd 1) j
  rcases hj with rfl | rfl
  · refine ⟨d,?_,?_⟩
    · intro x hx
      change (e (x.val.left 1),e (x.val.left (.ofAdd 1)))=_
      rw [hx]
      change (e planeRoot,e 1)=_
      rw [plane_root_mark,map_one]
    · intro x hx
      change (e (x.val.left 1),e (x.val.left (.ofAdd 1)))=_
      rw [hx]
      change (e planeRoot,e planeRoot)=_
      rw [plane_root_mark]
  · refine ⟨d.trans MulEquiv.prodComm,?_,?_⟩
    · intro x hx
      change (e (x.val.left (.ofAdd 1)),e (x.val.left 1))=_
      rw [hx]
      change (e planeRoot,e 1)=_
      rw [plane_root_mark,map_one]
    · intro x hx
      change (e (x.val.left (.ofAdd 1)),e (x.val.left 1))=_
      rw [hx]
      change (e planeRoot,e planeRoot)=_
      rw [plane_root_mark]

/-- The short centralizer comparison retains both its short root and the whole-Sylow central root. -/
theorem exists_marked_cyclic_centralizer (f z : PlaneWreath) (u : V4)
    (hu : orderOf (baseMap u)=2) (hc : ⁅baseMap.range,zpowers f⁆=zpowers (baseMap u))
    (hz : z∈center PlaneWreath) (hz1 : z≠1) :
    ∃ d : centralizer ({baseMap u} : Set PlaneWreath) ≃* DihedralGroup 4 × DihedralGroup 4,
      (∀ x, x.val=baseMap u → d x=(DihedralGroup.r 2,1)) ∧
      (∀ x, x.val=z → d x=(DihedralGroup.r 2,DihedralGroup.r 2)) := by
  have hzr := root_test z (fun y => (mem_center_iff.mp hz y).symm) hz1
  rw [hzr]
  obtain ⟨haxis,_⟩ := SylowGraphCenter.displacement_of_cyclic_base_commutator f u hu hc
  rcases haxis with rfl | rfl
  all_goals exact exists_marked_axis_centralizer _
end BinaryPermutation.AlternatingFiveExtension.SylowCommutator
