module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.CorePlacement
/-!
# Faithful local component actions

Once the opposite core lies in K, the characteristic-two centralizer bound
and the core faithfulness theorem make G₂ act faithfully on K. The first
residual is cubic and contained in the centerless K, so it cannot centralize K.
F.6.7 then places the first action kernel in its two-core, hence in the common
Sylow subgroup and in G₂. Thus the first action is faithful as well.

Source: Aschbacher--Smith F.6.17, printed p.309. The faithful actions here
retain the original local embeddings and actual component.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem SingleResidualComponent.local_disjoint_centralizer (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hz : center d.component = ⊥)
    (hQK : (pCore 2 G₂).map G₂.subtype ≤ d.component)
    (hgood : generalizedFitting G₂ = pCore 2 G₂)
    (hthree : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    Disjoint G₁ (centralizer (d.component : Set G)) ∧
      Disjoint G₂ (centralizer (d.component : Set G)) := by
  let K := d.component
  change center K = ⊥ at hz
  let C := centralizer (K : Set G)
  let : K.Normal := d.normal
  have hc := d.core_disjoint_centralizer hcore
  have hd₂ : Disjoint G₂ C := by
    apply disjoint_def.mpr
    intro x hx hxC
    have hx' : (⟨x,hx⟩ : G₂) ∈ centralizer (pCore 2 G₂ : Set G₂) := by
      intro q hq
      apply Subtype.ext
      exact hxC q (hQK ⟨q,hq,rfl⟩)
    have hxQ := h.symm.local_core_selfCentralizing hgood hx'
    exact hc.le_bot ⟨⟨⟨x,hx⟩,hxQ,rfl⟩,hxC⟩
  have hLnot : ¬ (pResidual 2 G₁).map G₁.subtype ≤ C := by
    intro hLC
    have hb : (pResidual 2 G₁).map G₁.subtype = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hxK := d.left_contains hx
      have hxZ : (⟨x,hxK⟩ : K) ∈ center K :=
        mem_center_iff.mpr (fun k => Subtype.ext (hLC hx k k.property))
      have h1 : (⟨x,hxK⟩ : K) = 1 := by simpa only [hz,mem_bot] using hxZ
      exact congrArg (fun k : K => (k : G)) h1
    simp [hb] at hthree
  have hleft := (h.left_subnormal_core_iff_not_residual_le C
    (inferInstance : C.Normal).isSubnormal).mpr hLnot
  refine ⟨?_,hd₂⟩
  apply disjoint_def.mpr
  intro x hx hxC
  have hxQ := hleft ⟨hx,hxC⟩
  exact hd₂.le_bot ⟨(h.local_twoCore_le_intersection hxQ).2,hxC⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
