module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PPerfectHom

/-!
# The canonical component of the character kernel

If K/O₂(K) is the concrete SL₃(2), the solvable residual of K is the
canonical C-component lifted through O₂(K) by A.3.3(4). It surjects onto
the quotient, and O₂(K) supplements it. Core intersection and generalized
Fitting identities use relative normality inside K throughout.

Source: Aschbacher–Smith, A.3.3(3)–(4), printed pp.42–43, and C.1.37,
printed pp.141–143, for the repair of 15.3.68(2).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

variable {K : Type*} [Group K] [Finite K]

theorem residual_isCComponent (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    (solvableResidual K).IsCComponent := by
  let : IsSimpleGroup (K ⧸ pCore 2 K) := by
    let := Atlas.Comparisons.Exceptional.sl3Two_simple
    exact e.isSimpleGroup
  let : Group.IsPerfect (K ⧸ pCore 2 K) := by
    let := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup (⊤ : Subgroup (K ⧸ pCore 2 K)) := topEquiv.isSimpleGroup
  have ht : (⊤ : Subgroup (K ⧸ pCore 2 K)).IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect .top
  let : Group.IsNilpotent (pCore 2 K) := (pCore_isPGroup (p := 2) (G := K)).isNilpotent
  have hc := ht.solvableResidual_preimage (pCore 2 K)
  rw [comap_top, map_solvableResidual_eq _ topEquiv.surjective] at hc
  exact hc

theorem residual_quotient_image (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    (solvableResidual K).map (QuotientGroup.mk' (pCore 2 K)) = ⊤ := by
  let : Group.IsPerfect (K ⧸ pCore 2 K) := by
    let := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rw [map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _), solvableResidual_eq_top]

omit [Finite K] in
theorem sup_sylow_eq_top (L : Subgroup K) [L.Normal] (hsup : L ⊔ pCore 2 K = ⊤)
    (S : Sylow 2 K) : L ⊔ (S : Subgroup K) = ⊤ := by
  exact top_unique (hsup ▸ sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) L)

theorem core_intersection (L : Subgroup K) (hL : L.IsCComponent) :
    pCore 2 K ⊓ L = (pCore 2 L).map L.subtype := by
  rw [pCore_subnormal_eq_comap 2 hL.subnormal, map_comap_eq, L.range_subtype, inf_comm]

theorem fitting_eq_core (U : Subgroup K) (hU : U ≤ pCore 2 K)
    (hc : centralizer (U : Set K) = pCore 2 K) : generalizedFitting K = pCore 2 K := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (centralizer_le hU).trans hc.le

omit [Finite K] in
theorem twoPerfect_le_component (L X : Subgroup K) [L.Normal] (hsup : L ⊔ pCore 2 K = ⊤)
    (hX : IsPPerfect 2 X) : X ≤ L := by
  have hp := isPGroup_quotient_of_sup_eq_top L (pCore 2 K) pCore_isPGroup hsup
  have h := hX.hom_eq_one_of_isPGroup hp ((QuotientGroup.mk' L).comp X.subtype)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  exact congrArg (fun f : X →* K ⧸ L => f ⟨x,hx⟩) h
/-- The canonical lift together with the core generates K. -/
theorem residual_sup_core (e : (K ⧸ pCore 2 K) ≃*
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    solvableResidual K ⊔ pCore 2 K = ⊤ := by
  have h := congrArg (comap (QuotientGroup.mk' (pCore 2 K))) (residual_quotient_image e)
  simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using h

/-- The R₂ quotient condition follows from the genuine centralizer equality. -/
theorem reduced_quotient_core (U : Subgroup K) [U.Normal]
    (hc : centralizer (U : Set K) = pCore 2 K) :
    pCore 2 (K ⧸ centralizer (U : Set K)) = ⊥ := by
  have h : ∀ N : Subgroup K, ∀ hn : N.Normal, N = pCore 2 K →
      @pCore 2 (K ⧸ N) (@QuotientGroup.Quotient.group _ _ N hn) = ⊥ := by
    intro N hn he
    subst N
    exact pCore_quotient_pCore_eq_bot 2
  exact h _ inferInstance hc

theorem component_quotient_iso (L : Subgroup K) (hL : L.IsCComponent)
    (hmap : L.map (QuotientGroup.mk' (pCore 2 K)) = ⊤)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  exact ⟨(cComponentTwoCoreQuotientEquiv hL).trans
    ((MulEquiv.subgroupCongr hmap).trans (topEquiv.trans e))⟩

theorem quotient_conjugation_inner (L : Subgroup K) [L.Normal]
    (hmap : L.map (QuotientGroup.mk' (pCore 2 K)) = ⊤) :
    ∀ k : K, ∃ l : L, ∀ x : L,
      QuotientGroup.mk' (pCore 2 L) (MulAut.conjNormal k x) =
      QuotientGroup.mk' (pCore 2 L) (l * x * l⁻¹) := by
  intro k
  let q := QuotientGroup.mk' (pCore 2 K)
  obtain ⟨l,hl,hq⟩ := (show q k ∈ L.map q from hmap ▸ mem_top _)
  refine ⟨⟨l,hl⟩, fun x => ?_⟩
  apply QuotientGroup.eq.mpr
  rw [pCore_subnormal_eq_comap 2 (inferInstance : L.Normal).isSubnormal]
  change (MulAut.conjNormal k x : L)⁻¹ * (⟨l,hl⟩ * x * ⟨l,hl⟩⁻¹) ∈
    (pCore 2 K).comap L.subtype
  change (k * (x : K) * k⁻¹)⁻¹ * (l * (x : K) * l⁻¹) ∈ pCore 2 K
  apply (QuotientGroup.eq_one_iff _).mp
  change q ((k * (x : K) * k⁻¹)⁻¹ * (l * (x : K) * l⁻¹)) = 1
  simp only [map_mul, map_inv, hq, inv_mul_cancel]
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
