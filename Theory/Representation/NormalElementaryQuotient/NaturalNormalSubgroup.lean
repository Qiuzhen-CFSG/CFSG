module
public import Theory.Representation.NormalElementaryQuotient
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Normal subgroups of a central extension of the natural SL₂ module

Suppose an elementary normal subgroup V maps equivariantly onto the natural
SL₂ module and the projection kernel is precisely its central part. A normal
subgroup W of V either lies in that kernel or covers the quotient: SL₂ is
transitive on nonzero vectors, so one nonzero image generates every image
by conjugation. The resulting equality retains the full central attachment.

Source application: DGS, Groups and Graphs (1985), the first dichotomy in
6.5, printed p.121, applied to Z_lambda inside the original Baumann module.
-/

open Subgroup
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace Representation.NormalElementaryQuotient
variable {G F : Type*} [Group G] [Field F] [Algebra (ZMod 2) F]

/-- A normal subgroup is central or covers the same natural quotient. -/
theorem normal_subgroup_alternative_of_natural_projection
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (f : Additive V →ₗ[ZMod 2] (Fin 2 → F))
    (hker : ∀ v, f v = 0 ↔ (v.toMul : G) ∈ center G)
    (he : ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
      Matrix.mulVec (q g).val (f v))
    (W : Subgroup G) [W.Normal] (hWV : W ≤ V) :
    W ≤ center G ∨ W ⊔ (V ⊓ center G) = V := by
  by_cases hWc : W ≤ center G
  · exact Or.inl hWc
  right
  obtain ⟨w,hw,hwc⟩ := SetLike.not_le_iff_exists.mp hWc
  let w' : Additive V := Additive.ofMul ⟨w,hWV hw⟩
  have hfw : f w' ≠ 0 := fun hz => hwc ((hker w').mp hz)
  apply le_antisymm (sup_le hWV inf_le_left)
  intro v hv
  let v' : Additive V := Additive.ofMul ⟨v,hv⟩
  by_cases hfv : f v' = 0
  · exact (show V ⊓ center G ≤ W ⊔ (V ⊓ center G) from le_sup_right)
      ⟨hv,(hker v').mp hfv⟩
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq F (f w') (f v') hfw hfv
  obtain ⟨g,rfl⟩ := hq a
  let u : Additive V := Additive.ofMul (MulAut.conjNormal g w'.toMul)
  have hu : (u.toMul : G) ∈ W := (inferInstance : W.Normal).conj_mem w hw g
  have hfu : f u = f v' := (he g w').trans ha
  have hzero : f (v'-u) = 0 := by rw [map_sub,hfu,sub_self]
  have hc : ((v'-u).toMul : G) ∈ V ⊓ center G :=
    ⟨(v'-u).toMul.property,(hker (v'-u)).mp hzero⟩
  have hh := (W ⊔ (V ⊓ center G)).mul_mem
    ((show V ⊓ center G ≤ W ⊔ (V ⊓ center G) from le_sup_right) hc)
    ((show W ≤ W ⊔ (V ⊓ center G) from le_sup_left) hu)
  change (v / (u.toMul : G)) * (u.toMul : G) ∈ W ⊔ (V ⊓ center G) at hh
  simpa only [div_mul_cancel] using hh
end Representation.NormalElementaryQuotient
