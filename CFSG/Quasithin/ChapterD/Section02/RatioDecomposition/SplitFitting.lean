module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Split
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.Fitting.Core
public import Mathlib.LinearAlgebra.Projection
/-!
# Full Fitting movement in the literal ratio factors

The internal direct product supplies a surjective group projection to each
factor. The complementary vector-space projection intertwines the original
action with the corresponding literal factor action. A surjective group map
sends the Fitting subgroup into the target Fitting subgroup, so projecting the
original full Fitting moved space gives full Fitting movement on each summand.

This discharges the recursive D.2.17 input after a D.2.16 split, retaining the
actual subgroup carriers and restricted actions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, D.2.16–17,
printed pp.187–188 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem fitting_image_le {H : Type*} [Group H] (p : G →* H)
    (hp : Function.Surjective p) : (fittingSubgroup G).map p ≤ fittingSubgroup H := by
  have hn : ((fittingSubgroup G).map p).Normal :=
    (inferInstance : (fittingSubgroup G).Normal).map p hp
  have hnil : Group.IsNilpotent ((fittingSubgroup G).map p) :=
    Group.nilpotent_of_surjective (p.subgroupMap (fittingSubgroup G))
      (p.subgroupMap_surjective (fittingSubgroup G))
  exact le_sSup ⟨hn,hnil⟩

private theorem quotient_fitting_full {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) H W) (p : G →* H) (hp : Function.Surjective p)
    (e : V →ₗ[ZMod 2] W) (he : Function.Surjective e)
    (hact : ∀ g v, e (ρ g v) = σ (p g) (e v))
    (hfull : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    subspaceCommutator σ ⊤ (fittingSubgroup H) = ⊤ := by
  have hm := subspaceCommutator_map_embedding (σ.comp p) ρ (MonoidHom.id G)
    e (fun g v => (hact g v).symm) (fittingSubgroup G) ⊤
  have he' : e.range = ⊤ := LinearMap.range_eq_top.mpr he
  simp only [Submodule.map_top,he',Subgroup.map_id,hfull] at hm
  rw [subspaceCommutator_comp_map] at hm
  apply top_unique
  apply hm.ge.trans
  apply Submodule.span_mono
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact ⟨g,fitting_image_le p hp hg,v,hv,rfl⟩

private theorem factor_fitting_full
    {H K : Subgroup G} {U W : Submodule (ZMod 2) V}
    (d : FactorData ρ H U) (k : FactorData ρ K W)
    (hcompl : IsCompl U W) (hdis : Disjoint H K) (hsup : H ⊔ K = ⊤)
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, Commute x y)
    (hfixU : U ≤ fixedSpace ρ K) (hfixW : W ≤ fixedSpace ρ H)
    (hfull : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    subspaceCommutator d.representation ⊤ (fittingSubgroup H) = ⊤ := by
  have hc : H ≤ centralizer (K : Set G) := by
    intro x hx y hy
    exact (hcomm x hx y hy).symm
  obtain ⟨e₀,he₀⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting H K hdis hc
  let e : H × K ≃* G := e₀.trans ((MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv)
  have he (a : H) (b : K) : e (a,b) = (a:G) * (b:G) := he₀ a b
  let p : G →* H := (MonoidHom.fst H K).comp e.symm.toMonoidHom
  have hp (a : H) (b : K) : p (e (a,b)) = a := congrArg Prod.fst (e.symm_apply_apply (a,b))
  have hps : Function.Surjective p := fun a => ⟨e (a,1),hp a 1⟩
  let π := U.projectionOnto W hcompl
  apply quotient_fitting_full ρ d.representation p hps π
    (Submodule.projectionOnto_surjective hcompl) _ hfull
  intro g v
  obtain ⟨⟨a,b⟩,rfl⟩ := e.surjective g
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ W from hcompl.sup_eq_top ▸ Submodule.mem_top)
  have hbu : ρ (b:G) u = u := hfixU hu b
  have habw : ρ (a:G) (ρ (b:G) w) = ρ (b:G) w :=
    hfixW (by rw [← k.equivariant b ⟨w,hw⟩]; exact (k.representation b ⟨w,hw⟩).property) a
  have hpa : π (ρ (a:G) u) = d.representation a ⟨u,hu⟩ := by
    rw [← d.equivariant a ⟨u,hu⟩]
    exact Submodule.projectionOnto_apply_left hcompl _
  have hpb : π (ρ (b:G) w) = 0 := by
    rw [← k.equivariant b ⟨w,hw⟩]
    exact Submodule.projectionOnto_apply_right hcompl _
  have hpu : π u = ⟨u,hu⟩ := Submodule.projectionOnto_apply_left hcompl ⟨u,hu⟩
  have hpw : π w = 0 := Submodule.projectionOnto_apply_right hcompl ⟨w,hw⟩
  rw [hp,he,map_mul,Module.End.mul_apply,map_add,map_add,hbu,habw,
    map_add,hpa,hpb,map_add,hpu,hpw,add_zero,add_zero]

/-- Both literal factor actions retain the original full Fitting moved hypothesis. -/
theorem fitting_full_of_split
    {G₁ G₂ : Subgroup G} {V₁ V₂ : Submodule (ZMod 2) V}
    (d₁ : FactorData ρ G₁ V₁) (d₂ : FactorData ρ G₂ V₂)
    (h : IsRatioSum ρ G₁ G₂ V₁ V₂)
    (hd : Disjoint G₁ G₂) (hs : G₁ ⊔ G₂ = ⊤)
    (hc : ∀ x ∈ G₁, ∀ y ∈ G₂, Commute x y)
    (hfull : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    subspaceCommutator d₁.representation ⊤ (fittingSubgroup G₁) = ⊤ ∧
    subspaceCommutator d₂.representation ⊤ (fittingSubgroup G₂) = ⊤ := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hcompl,_,_,hcross₁,hcross₂⟩ := h
  have hfix₁ := (subspaceCommutator_eq_bot_iff ρ V₂ G₁).mp hcross₁
  have hfix₂ := (subspaceCommutator_eq_bot_iff ρ V₁ G₂).mp hcross₂
  exact ⟨factor_fitting_full ρ d₁ d₂ hcompl hd hs hc hfix₂ hfix₁ hfull,
    factor_fitting_full ρ d₂ d₁ hcompl.symm hd.symm (sup_comm G₂ G₁ ▸ hs)
      (fun x hx y hy => (hc y hy x hx).symm) hfix₁ hfix₂ hfull⟩

end CFSG.Quasithin.ChapterD.RatioDecomposition
