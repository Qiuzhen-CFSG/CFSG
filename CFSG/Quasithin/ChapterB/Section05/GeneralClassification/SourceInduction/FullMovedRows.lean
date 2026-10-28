module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairModule

/-!
# Fully moved modules exclude the exceptional B.5 factor

Projecting the original module onto either quotient summand intertwines its
full action with the corresponding factor. Thus full commutator generation
of the module implies full commutator generation of each quotient summand.
The exceptional B.4.8 four-space has a three-dimensional moved space, so it
cannot occur. The natural and doubled rows retain their original subspaces.

The application in Chapter10.PointControl.Selection.ModuleChoice uses the
actual full module, which satisfies [V,L₀] = V, to recognize its binary-three
factor before transporting coordinates to [V,L]/C_[V,L](L).
Source: Aschbacher--Smith B.4.8(3), B.5.6(3), 3.2.6(3a) and10.1.1,
printed pp.91,105,581,741.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V}

/-- Full movement descends to the original quotient summand and its factor. -/
theorem SourceTwoFactorCase.first_quotient_moved_eq_top (d : SourceTwoFactorCase ρ)
    (hm : moved ρ ⊤ = ⊤) :
    moved (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) ⊤ = ⊤ := by
  let U := (fixed ρ).quotientImage d.firstSpace
  let W := (fixed ρ).quotientImage d.secondSpace
  let τ := (fixed ρ).quotientRepresentation
  let p := U.toSubmodule.projectionOnto W.toSubmodule d.decomposition
  let f := p.comp (fixed ρ).toSubmodule.mkQ
  have hp : Function.Surjective p := fun u => ⟨u,Submodule.projectionOnto_apply_left d.decomposition u⟩
  have hf : Function.Surjective f := hp.comp (fixed ρ).toSubmodule.mkQ_surjective
  have hpact (g : Q) (v : V ⧸ (fixed ρ).toSubmodule) : p (τ g v) = U.toRepresentation g (p v) := by
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ U.toSubmodule ⊔ W.toSubmodule from d.decomposition.sup_eq_top ▸ Submodule.mem_top)
    have hgu := U.apply_mem_toSubmodule g hu
    have hgw := W.apply_mem_toSubmodule g hw
    have hpu : p u = ⟨u,hu⟩ := Submodule.projectionOnto_apply_of_mem_left
      (p := U.toSubmodule) (q := W.toSubmodule) d.decomposition hu
    have hpw : p w = 0 := Submodule.projectionOnto_apply_of_mem_right
      (p := U.toSubmodule) (q := W.toSubmodule) d.decomposition hw
    have hpgu : p (τ g u) = ⟨τ g u,hgu⟩ := Submodule.projectionOnto_apply_of_mem_left
      (p := U.toSubmodule) (q := W.toSubmodule) d.decomposition hgu
    have hpgw : p (τ g w) = 0 := Submodule.projectionOnto_apply_of_mem_right
      (p := U.toSubmodule) (q := W.toSubmodule) d.decomposition hgw
    simp only [map_add,hpu,hpw,hpgu,hpgw,add_zero]
    rfl
  have hfact (g : Q) (v : V) : f (ρ g v) =
      U.toRepresentation (d.product.fst g : Q) (f v) := by
    change p ((fixed ρ).toSubmodule.mkQ (ρ g v)) = _
    rw [←Subrepresentation.quotientRepresentation_mk (fixed ρ),hpact]
    obtain ⟨a,b,rfl⟩ := d.product.exists_mul g
    rw [d.product.fst_apply,map_mul,Module.End.mul_apply]
    exact congrArg (U.toRepresentation a) (d.second_fixes_first b (f v))
  let σ := U.toRepresentation.comp d.first.subtype
  have hle : (moved ρ ⊤).map f ≤ moved σ ⊤ := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    change f (ρ g v - v) ∈ moved σ ⊤
    rw [map_sub,hfact]
    exact Submodule.subset_span ⟨d.product.fst g,mem_top _,f v,Submodule.mem_top,rfl⟩
  rw [hm,Submodule.map_top,LinearMap.range_eq_top.mpr hf] at hle
  exact top_unique hle

private theorem no_four_dimensional_full_moved
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) H W}
    (c : FourDimensionalSource σ) (hm : moved σ ⊤ = ⊤) : False := by
  have hspace : c.space.toSubmodule = ⊤ := c.space_eq.trans hm
  have hd := c.natural.linearEquiv.finrank_eq
  have he : Module.finrank (ZMod 2) c.space.toSubmodule = Module.finrank (ZMod 2) W := by
    rw [hspace,finrank_top]
  rw [he,c.dimension] at hd
  have hthree : Module.finrank (ZMod 2) (Fin 3 → BinaryField.two.Carrier) = 3 :=
    Module.finrank_fin_fun (ZMod 2)
  rw [hthree] at hd
  omega

/-- The exceptional four-space cannot occur in a fully moved source module. -/
theorem SourceTwoFactorCase.first_ordinary_of_moved_eq_top (d : SourceTwoFactorCase ρ)
    (hm : moved ρ ⊤ = ⊤) :
    d.firstSpace.toSubmodule = moved ρ d.first ∧
      (FactorNatural (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) ∨
        ∃ F : BinaryField, Odd F.degree ∧ IsRepeatedLinearNatural
          (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) F 3 2) := by
  cases d.firstCase with
  | natural he hn => exact ⟨he,Or.inl hn⟩
  | doubleNatural F ho he hn => exact ⟨he,Or.inr ⟨F,ho,hn⟩⟩
  | exceptional _ c => exact (no_four_dimensional_full_moved c (d.first_quotient_moved_eq_top hm)).elim

end CFSG.Quasithin.ChapterB.SourceInduction
