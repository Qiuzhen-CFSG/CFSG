module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.FundamentalHypothesis
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
import Mathlib.Tactic
/-!
# The actual covering residual is a C-component

The normal two-perfect cover maps onto the original quasisimple quotient
with a two-group kernel. C-component lifting through that literal quotient
makes it a C-component of the actual intersection. The source specialization
uses the previously proved equality of the two-residual and perfect residual.
Source: Aschbacher--Smith,4.2.4 and C.2.8(2), printed p.608 and p.147.
-/

public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- A normal two-perfect cover of the actual quasisimple core quotient is
a genuine C-component, through its literal quotient homomorphism. -/
theorem normal_cover_isCComponent {X A Y : Subgroup G}
    (hYA : Y ≤ A) (hYX : Y ≤ X) (hYN : (Y.subgroupOf A).Normal)
    (hY : IsPPerfect 2 Y) [IsQuasisimple (X ⧸ pCore 2 X)]
    (hcover : (X : Set G) = (Y : Set G) * (X.pCoreIn 2 : Set G)) :
    (Y.subgroupOf A).IsCComponent := by
  let f : Y →* X ⧸ pCore 2 X := (QuotientGroup.mk' (pCore 2 X)).comp (inclusion hYX)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
    obtain ⟨y,hy,c,hc,he⟩ := hcover ▸ (show x.val ∈ (X : Set G) from x.property)
    refine ⟨⟨y,hy⟩,?_⟩
    apply QuotientGroup.eq.mpr
    obtain ⟨c',hc',hc'eq⟩ := hc
    have hec : (⟨y,hYX hy⟩ : X)⁻¹ * x = c' := by
      apply Subtype.ext
      change y⁻¹ * x.val = c'.val
      rw [← he,← hc'eq]
      simp only [Subgroup.subtype_apply]
      group
    change (⟨y,hYX hy⟩ : X)⁻¹ * x ∈ pCore 2 X
    rwa [hec]
  let j : f.ker →* pCore 2 X :=
    { toFun := fun z => ⟨⟨z.val.val,hYX z.val.property⟩,
        (QuotientGroup.eq_one_iff _).mp z.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 X => x.val.val) hab))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective j hj
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : IsQuasisimple (Y ⧸ f.ker) := IsQuasisimple.of_mulEquiv e.symm
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient f.ker hk hY
  let u : Y ≃* Y.subgroupOf A := (subgroupOfEquivOfLe hYA).symm
  have hu := ht.map_equiv u
  have he : (⊤ : Subgroup Y).map u.toMonoidHom = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr u.surjective
  rw [he] at hu
  simpa only [← MonoidHom.range_eq_map,range_subtype] using hu.map_subtype hYN.isSubnormal

/-- The literal LH=(L∩H)^infinity in the original normalized source is a
C-component of H∩N(L). Its covering and quotient premises are proved. -/
theorem source_intersection_isCComponent {K : GroupClass} {T : Sylow 2 G}
    {L J H : Subgroup G} (h : Chapter12.Section02.Hypothesis1221 K T L)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H) :
    (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf
      (H ⊓ normalizer (L : Set G))).IsCComponent := by
  have hyp := source_hypothesis411 h hM
  obtain ⟨hc,hY,hYN⟩ := residual_cover_of_containment hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hcover hJH
  let := h.quasisimple
  have hh := normal_cover_isCComponent hY ((map_subtype_le _).trans inf_le_left)
    hYN (isPPerfect_embedded_pResidual 2 (L ⊓ H)) hc
  rw [Chapter4.Section04.chosen_intersection_twoResidual_eq_solvableResidual h hcover hJH] at hh
  exact hh
end CFSG.Quasithin.Chapter4.Section02.Unitary
