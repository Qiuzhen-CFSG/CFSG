module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry
public import Theory.Representation.BinaryOffender.HyperplaneFixer
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Identifying the first parabolic core with the source centralizer

An element of C_S(V₂) fixes Z₁V₂, an order-eight subgroup of the original
order-sixteen module V. The quadratic ratio two excludes a nontrivial
two-group image fixing this hyperplane. Thus C_S(V₂)=C_T(V).
Combining this with the first-plane action calculation identifies O₂(P₀)
on the same natural flag, without assuming any parabolic conclusion.

Source: Aschbacher--Smith, 15.1.29, printed p.1104 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal IsMulCommutative
open CFSG.Quasithin.ChapterD.UniqueFactor
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem centralizes_of_fixed_hyperplane
    (h : PreparedChosenModule T M V) (H W : Subgroup G)
    (hHM : H ≤ M) (hH : IsPGroup 2 H) (hWV : W ≤ V)
    (hc : H ≤ centralizer (W : Set G))
    (hVcard : Nat.card V = 16) (hWcard : Nat.card W = 8) :
    H ≤ centralizer (V : Set G) := by
  let := h.elementary
  let f := (actionHom M V h.normalized).rangeRestrict
  let ρ := imageRepresentation M V h.normalized
  let A := (H.subgroupOf M).map f
  have hAp : IsPGroup 2 A := hH.comap_subtype.map f
  let e : W → fixedSpace ρ A := fun w =>
    ⟨Additive.ofMul ⟨w.val,hWV w.property⟩,by
      intro a
      obtain ⟨x,hx,he⟩ := a.property
      have he' : a = ⟨f x,mem_map_of_mem f hx⟩ := Subtype.ext he.symm
      subst a
      apply Additive.toMul.injective
      apply Subtype.ext
      change x.val * w.val * x.val⁻¹ = w.val
      have hh : w.val * x.val = x.val * w.val := hc hx w.val w.property
      rw [← hh,mul_inv_cancel_right]⟩
  have hei : Function.Injective e := by
    intro x y he
    exact Subtype.ext (congrArg (fun v : fixedSpace ρ A => v.val.toMul.val) he)
  have hcard := Nat.card_le_card_of_injective e hei
  rw [hWcard,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
  have hdim : Module.finrank (ZMod 2) (Additive V) = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hcV := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, Nat.card_congr Additive.toMul, hVcard] at hcV
    exact hcV.symm
  have hdimF : 3 ≤ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    by_contra hh
    have hb : Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2 := by omega
    have hb' := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    norm_num at hb'
    omega
  have hq : 1 < quadraticRatio ρ := by rw [h.quadratic_ratio]; norm_num
  have hzero : A = ⊥ := twoSubgroup_eq_bot_of_fixedCodim_le_one ρ hq A hAp (by
    have := fixedCodim_add_finrank ρ A
    omega)
  intro x hx
  have hf : f ⟨x,hHM hx⟩ = 1 := by
    have hh := mem_map_of_mem f (show (⟨x,hHM hx⟩ : M) ∈ H.subgroupOf M from hx)
    change f ⟨x,hHM hx⟩ ∈ A at hh
    simpa only [hzero,mem_bot] using hh
  have hk : (⟨x,hHM hx⟩ : M) ∈ (actionHom M V h.normalized).ker :=
    congrArg Subtype.val hf
  rwa [actionHom_ker] at hk

/-- The actual moving-plane centralizer equals the source full-module centralizer. -/
theorem NineSource.sylow_plane_centralizer_eq {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) :
    d.S ⊓ centralizer (d.nineMovingPlane : Set G) =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let := h.elementary
  have hFV : d.nineFixedPlane ≤ V := le_sup_left.trans_eq s.planes_sup
  have hWV : d.nineMovingPlane ≤ V := le_sup_right.trans_eq s.planes_sup
  have hZV : d.Z1 ≤ V := s.marked_le_fixed.trans hFV
  have hcomm {A B : Subgroup G} (hA : A ≤ V) (hB : B ≤ V) :
      B ≤ normalizer (A : Set G) :=
    (hB.trans (V.le_centralizer.trans (centralizer_le hA))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdis : Disjoint d.nineFixedPlane d.nineMovingPlane := disjoint_iff.mpr s.planes_inf
  have hVcard : Nat.card V = 16 := by
    rw [← s.planes_sup,card_sup_eq_mul_of_normalizes_of_disjoint _ _ (hcomm hFV hWV) hdis,
      s.fixed_card,s.moving_card]
  have hcard : Nat.card (d.Z1 ⊔ d.nineMovingPlane : Subgroup G) = 8 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ (hcomm hZV hWV)
      (hdis.mono_left s.marked_le_fixed),s.marked_card,s.moving_card]
  apply le_antisymm
  · refine le_inf (inf_le_left.trans d.S_le_T) ?_
    apply centralizes_of_fixed_hyperplane h _ (d.Z1 ⊔ d.nineMovingPlane)
      ((inf_le_left.trans d.S_le_T).trans hM.1.2)
      (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) (sup_le hZV hWV) _ hVcard hcard
    exact le_centralizer_iff.mpr (sup_le
      (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
      (le_centralizer_iff.mp inf_le_right))
  · exact le_inf (le_inf inf_le_left (inf_le_right.trans (centralizer_le hZV)))
      (inf_le_right.trans (centralizer_le hWV))
namespace NaturalFlag
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The first natural parabolic has the original source core C_T(V). -/
theorem first_core (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    a.parabolics.P0.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model (small_binary_model_of_marking hn e)
  exact (a.first_core_eq_sylow_plane_centralizer hs.1 d.nineMovingPlane
    (d.nineMovingPlane_le_UL s hG h hf t ht htS)
    (a.movingPlane_cut hG hM hu h hs ht htS hnat)).trans
      (s.sylow_plane_centralizer_eq hM h)

end NaturalFlag
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
