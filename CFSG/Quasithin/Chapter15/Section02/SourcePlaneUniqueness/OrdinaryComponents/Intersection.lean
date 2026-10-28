module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.ResidualRank
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The original H intersection with an escaping ordinary component

The wreath quotient makes H solvable. Its intersection with the actual
component contains the restriction of S, a full component Sylow, and is
fixed by the marked central involution. When the component is the literal
O^{3′}(I), the original K embeds in this intersection and forces three-rank
two. The Ree and triality consumers establish that residual identity.
Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

/-- The literal intersection of H with the ordinary component inside I. -/
def componentIntersection : Subgroup c.component :=
  H.comap (I.subtype.comp c.component.subtype)

include d
/-- The original wreath quotient makes H solvable. -/
theorem source_H_solvable : Group.IsSolvable H := by
  obtain ⟨e⟩ := d.geometry.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk',range_subtype])

/-- The same intersection is solvable, without a model assumption. -/
theorem component_intersection_solvable : Group.IsSolvable (componentIntersection (H := H) c) := by
  let : Group.IsSolvable H := source_H_solvable d
  let f : componentIntersection (H := H) c →* H := {
    toFun x := ⟨((x.val : I) : G),x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : H => (w : G)) h
  exact Group.isSolvable_of_isSolvable_injective hf

/-- Restriction of the actual S to its subnormal component supplies the full Sylow. -/
theorem component_intersection_sylow
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS) :
    ∃ Q : Sylow 2 c.component, (Q : Subgroup c.component) ≤ componentIntersection (H := H) c := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal c.component c.isComponent.1
  refine ⟨Q,?_⟩
  intro x hx
  have hxP : (x : I) ∈ P := by rw [hQ] at hx; exact hx
  have hxT : ((x : I) : G) ∈ (T : Subgroup G) :=
    (show planeSylow T ZS ≤ (T : Subgroup G) from inf_le_left)
      (hP ▸ mem_map_of_mem I.subtype hxP)
  exact d.geometry.outside.1.1.2 hxT

/-- Once the original cubic residual is identified, K forces rank two in H∩L. -/
theorem component_intersection_three_rank (hI : PlaneEscapes Mc ZS I)
    (hres : c.component = primeToResidual 3 I) :
    2 ≤ primeRank 3 (componentIntersection (H := H) c) := by
  let K := (pResidual 2 H).map H.subtype
  have hKL : K ≤ c.component.map I.subtype := by
    rw [hres]
    exact residual_le_escape_primeToResidual d hI
  let eL := c.component.equivMapOfInjective I.subtype I.subtype_injective
  let f : K →* c.component := eL.symm.toMonoidHom.comp (inclusion hKL)
  have hf (k : K) : ((f k : I) : G) = k := by
    exact congrArg Subtype.val (eL.apply_symm_apply ⟨k,hKL k.property⟩)
  let g : K →* componentIntersection (H := H) c := f.codRestrict _ (fun k => by
    change ((f k : I) : G) ∈ H
    rw [hf]
    exact map_subtype_le _ k.property)
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg (fun w : componentIntersection (H := H) c =>
      ((w.val : I) : G)) h).trans (hf y))
  have hbound := _root_.primeRank_le_of_injective 3 g hg
  rw [PlaneUniquenessPreceding.LinearThree.residual_rank_two d] at hbound
  exact hbound

/-- H lies in Mc=C_G(z), so the original marked action fixes the whole intersection. -/
theorem component_intersection_fixed (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    componentIntersection (H := H) c ≤ a.fixedSubgroup := by
  intro x hx
  rw [MulAut.mem_fixedSubgroup]
  apply Subtype.ext
  apply Subtype.ext
  rw [ha]
  have hc := (marked_centralizer d hI hz hzne).2.ge (d.geometry.in_partner hx)
  have hh : (x : G) * z = z * (x : G) := mem_centralizer_singleton_iff.mp hc
  rw [←hh,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
