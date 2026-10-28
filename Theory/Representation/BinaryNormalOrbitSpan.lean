module

public import Theory.Representation.BinaryIndexThreeOrbitSpan
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Normal closures and binary orbit spans

For the literal conjugation action on an elementary normal subgroup,
the normal closure of an element is its binary orbit span. The index-three
fixed-vector calculation therefore counts the actual normal closure.

Source: Aschbacher–Smith J.4.4(2), printed p.441.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G:Type*} [Group G] (R:Subgroup G) [IsElementaryAbelian 2 R]

/-- The linear orbit span counts the literal normal closure. -/
theorem card_normalClosure_eq_orbit_span
    (ρ:Representation (ZMod 2) G (Additive R))
    (heval:∀g v,((ρ g v).toMul:G)=g*(v.toMul:G)*g⁻¹) (x:R) :
    Nat.card (normalClosure ({(x:G)}:Set G))=
      Nat.card (Submodule.span (ZMod 2) (Set.range (fun g:G => ρ g (Additive.ofMul x)))) := by
  classical
  let E:=Submodule.span (ZMod 2) (Set.range (fun g:G => ρ g (Additive.ofMul x)))
  let P:Subgroup R := AddSubgroup.toSubgroup' E.toAddSubgroup
  let A:=P.map R.subtype
  have hinv (g:G) : ∀v∈E,ρ g v∈E := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h,rfl⟩:=hv
      exact Submodule.subset_span ⟨g*h,by
        change ρ (g*h) (Additive.ofMul x)=ρ g (ρ h (Additive.ofMul x))
        rw [map_mul];rfl⟩
    | zero => rw [map_zero];exact E.zero_mem
    | add u v _ _ hu hv => rw [map_add];exact E.add_mem hu hv
    | smul a v _ hv => rw [map_smul];exact E.smul_mem a hv
  let : A.Normal := ⟨by
    rintro a ⟨v,hv,rfl⟩ g
    exact ⟨(ρ g (Additive.ofMul v)).toMul,hinv g _ hv,heval g _⟩⟩
  have hxE : Additive.ofMul x∈E := by
    have h:ρ (1:G) (Additive.ofMul x)∈E:=Submodule.subset_span ⟨1,rfl⟩
    simpa only [map_one,Module.End.one_apply] using h
  have hNA : normalClosure ({(x:G)}:Set G)≤A :=
    normalClosure_le_normal (by rintro a rfl;exact ⟨x,hxE,rfl⟩)
  have hEN : E≤AddSubgroup.toZModSubmodule 2
      ((normalClosure ({(x:G)}:Set G)).subgroupOf R).toAddSubgroup := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    change ((ρ g (Additive.ofMul x)).toMul:G)∈normalClosure ({(x:G)}:Set G)
    rw [heval]
    exact Subgroup.Normal.conj_mem inferInstance (x:G) (subset_normalClosure (by simp)) g
  have hAN : A≤normalClosure ({(x:G)}:Set G) := by
    rintro a ⟨v,hv,rfl⟩
    exact hEN hv
  have he : normalClosure ({(x:G)}:Set G)=A := le_antisymm hNA hAN
  rw [he,show Nat.card A=Nat.card P from card_map_of_injective R.subtype_injective]
  let e:P≃E := {
    toFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
    invFun := fun v => ⟨v.val.toMul,v.property⟩
    left_inv := by intro v;rfl
    right_inv := by intro v;rfl }
  exact Nat.card_congr e

end Representation.BinaryOffender
