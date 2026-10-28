module
public import Theory.Representation.NormalPairHomogeneous

/-!
# Whole-module coordinates for separated homogeneous supports

The complementary support decomposition identifies the full module with the
product of its two supports. Applying the chosen homogeneous coordinates to
each support gives the literal separate factor action on the whole module.
This is the coordinate input for the small-multiplicity centralizer argument
in Aschbacher–Smith D.3.21; no multiplicity bound is needed here.
-/

public noncomputable section
namespace Representation.NormalPairHomogeneous
variable {k S Q V E : Type*} [Field k] [Group S] [Group Q]
  [AddCommGroup V] [Module k V] [AddCommGroup E] [Module k E]
  (ρ : Representation k Q V) (i : S × S →* Q) (σ : Representation k S E)

/-- Combining the two literal support coordinates gives coordinates on the
whole module. -/
def Coordinates.productEquiv (C : Coordinates ρ i σ)
    (h : IsCompl (NormalPairSupport.left ρ i) (NormalPairSupport.right ρ i)) :
    V ≃ₗ[k] ((Fin C.multiplicity → E) × (Fin C.multiplicity → E)) :=
  (Submodule.prodEquivOfIsCompl _ _ h).symm.trans (C.leftEquiv.prodCongr C.rightEquiv)

/-- The full pair acts separately on the two homogeneous coordinate blocks. -/
theorem Coordinates.productEquiv_intertwines (C : Coordinates ρ i σ)
    (h : IsCompl (NormalPairSupport.left ρ i) (NormalPairSupport.right ρ i))
    (d : S × S) (v : V) :
    C.productEquiv ρ i σ h (ρ (i d) v) =
      (fun j => σ d.1 ((C.productEquiv ρ i σ h v).1 j),
       fun j => σ d.2 ((C.productEquiv ρ i σ h v).2 j)) := by
  let a := Submodule.prodEquivOfIsCompl _ _ h
  obtain ⟨p,rfl⟩ := a.surjective v
  have hleft : ρ (i d) (p.1 : V) = (leftAction ρ i d.1 p.1 : V) := by
    change ρ (i d) (p.1 : V) = ρ (i (d.1,1)) (p.1 : V)
    have hd : d = (d.1,1)*(1,d.2) := by simp
    conv_lhs => rw [hd,map_mul,map_mul,Module.End.mul_apply]
    exact congrArg (ρ (i (d.1,1))) (p.1.property d.2)
  have hright : ρ (i d) (p.2 : V) = (rightAction ρ i d.2 p.2 : V) := by
    change ρ (i d) (p.2 : V) = ρ (i (1,d.2)) (p.2 : V)
    have hd : d = (1,d.2)*(d.1,1) := by simp
    conv_lhs => rw [hd,map_mul,map_mul,Module.End.mul_apply]
    exact congrArg (ρ (i (1,d.2))) (p.2.property d.1)
  have ha : ρ (i d) (a p) = a (leftAction ρ i d.1 p.1,rightAction ρ i d.2 p.2) := by
    change ρ (i d) ((p.1:V)+(p.2:V)) = _
    rw [map_add,hleft,hright]
    rfl
  rw [ha]
  change (C.leftEquiv.prodCongr C.rightEquiv)
      (a.symm (a (leftAction ρ i d.1 p.1,rightAction ρ i d.2 p.2))) =
    (fun j => σ d.1 (((C.leftEquiv.prodCongr C.rightEquiv) (a.symm (a p))).1 j),
     fun j => σ d.2 (((C.leftEquiv.prodCongr C.rightEquiv) (a.symm (a p))).2 j))
  simp only [a.symm_apply_apply,LinearEquiv.prodCongr_apply,C.left_intertwines,C.right_intertwines]

end Representation.NormalPairHomogeneous
