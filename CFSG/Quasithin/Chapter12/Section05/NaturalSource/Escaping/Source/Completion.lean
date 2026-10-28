module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.KernelCorank
public import Theory.SpecificGroups.SymmetricFive.RadicalRange

/-!
# Completing the terminal exterior construction from point escape

The selected H in XT has A₅/S₅ core quotient. Its minimal-parabolic core
has nilpotent image in that quotient; the absence of a nontrivial solvable
normal subgroup makes the full H-action kernel on U_H lie in O₂(H).
The literal flag action shows C_T(V₇) ≤ C_T(V). Thus this kernel also lies
in the quotient-centralizer X and hence in O₂(L₁H).

Together with the proved corank bound, actual escaping conjugate and
G.2.2 commutator estimate, this constructs TerminalConfiguration directly
and applies the original terminal contradiction. Only the point escape
G₁ ≰ M, proved by source 12.4.4, remains explicit. No extra local, fusion,
rank, action-kernel or escaping-conjugate premise is retained. Conversely,
every surviving exterior marking satisfies G₁ ≤ M; its exclusion remains
with this same task, qt-d-1251-source.

Source: Aschbacher--Smith, final paragraph of 12.5.1, printed p.822,
and the point-centralizer reduction 12.4.4, printed p.813.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE ChapterB
open Representation.SL5ExteriorSquare Representation.SL5TenDimensional

private theorem flag_eq_one_of_fixes_seven (g : Representation.SL5TenDimensional.Group)
    (hg : g ∈ flagGroup) (hfix : ∀ w ∈ V₇, exteriorAction 2 g w = w) : g = 1 := by
  open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry.SylowOvergroups in
  have hB : slEquivLinear 5 g ∈ standardBorel := by
    rwa [flagGroup_eq_standardBorel_comap] at hg
  have hu : g.val.IsUpperTriangular := by
    simpa only [BinaryLinear.FiveFlagGeometry.SylowOvergroups.matrix,
      MulEquiv.symm_apply_apply] using
      (BinaryLinear.FiveFlagGeometry.SylowOvergroups.mem_standardBorel_iff _).mp hB
  have hd (i : Fin 5) : g.val i i = 1 := by
    simpa only [BinaryLinear.FiveFlagGeometry.SylowOvergroups.matrix,
      MulEquiv.symm_apply_apply] using
      BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardBorel_diagonal hB i
  have hu' (i j : Fin 5) (hji : j < i) : g.val i j = 0 := hu hji
  have hc (t : Fin 10) (ht : t ∈ ({0,1,2,3,4,5,6} : Finset (Fin 10))) (i : Fin 10) :
      actionMatrix g i t = (Pi.single t 1 : Coordinates) i := by
    have he := congrArg coordinates (hfix (basis t)
      (Submodule.subset_span ⟨t,ht,rfl⟩))
    rw [coordinates_action,coordinates_basis,Matrix.mulVec_single_one] at he
    exact congrFun he i
  have h12 : g.val 1 2 = 0 := by simpa [actionMatrix,pair,hu',hd] using hc 1 (by decide) 0
  have h13 : g.val 1 3 = 0 := by simpa [actionMatrix,pair,hu',hd] using hc 2 (by decide) 0
  have h14 : g.val 1 4 = 0 := by simpa [actionMatrix,pair,hu',hd] using hc 3 (by decide) 0
  have h23 : g.val 2 3 = 0 := by simpa [actionMatrix,pair,hu',hd] using hc 2 (by decide) 1
  have h24 : g.val 2 4 = 0 := by simpa [actionMatrix,pair,hu',hd] using hc 3 (by decide) 1
  have h34 : g.val 3 4 = 0 := by simpa [actionMatrix,pair,hu',hd] using hc 3 (by decide) 2
  have h01 : g.val 0 1 = 0 := by simpa [actionMatrix,pair,hu',hd] using hc 4 (by decide) 1
  have h02 : g.val 0 2 = 0 := by simpa [actionMatrix,pair,hd,h12] using hc 4 (by decide) 0
  have h03 : g.val 0 3 = 0 := by simpa [actionMatrix,pair,hd,h13] using hc 5 (by decide) 0
  have h04 : g.val 0 4 = 0 := by simpa [actionMatrix,pair,hd,h14] using hc 6 (by decide) 0
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hu',hd,h12,h13,h14,h23,h24,h34,h01,h02,h03,h04]

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

omit [Finite G] in
/-- A Sylow element fixing the actual seven-space fixes the whole original V. -/
theorem sylow_centralizer_seven_le_seed :
    (T : Subgroup G) ⊓ centralizer (s.marking.Vi 7 : Set G) ≤ centralizer (V : Set G) := by
  intro t ht
  let tJ : (L ⊔ (T : Subgroup G) : Subgroup G) :=
    ⟨t,(show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) ht.1⟩
  have ha : s.actor tJ = 1 := by
    apply flag_eq_one_of_fixes_seven _ (s.sylow_flag ⟨t,ht.1⟩)
    intro w hw
    let v := s.marking.coordinates.symm (Multiplicative.ofAdd w)
    have hv : (v : G) ∈ s.marking.Vi 7 :=
      (s.marking.mem_subspace V₇ v).mpr
        (by simpa only [v,MulEquiv.apply_symm_apply,toAdd_ofAdd] using hw)
    have he := s.equivariant tJ v
    have htv : t * v * t⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (s.normalizes tJ.property) v).mp v.property
    have hv' : (⟨t * v * t⁻¹,htv⟩ : V) = v := by
      apply Subtype.ext
      change t * (v : G) * t⁻¹ = (v : G)
      rw [←ht.2 v hv,mul_inv_cancel_right]
    change s.marking.coordinates (⟨t * v * t⁻¹,htv⟩ : V) = _ at he
    rw [hv'] at he
    simpa only [v,MulEquiv.apply_symm_apply,toAdd_ofAdd] using
      (congrArg Multiplicative.toAdd he).symm
  intro v hv
  have he := s.equivariant tJ ⟨v,hv⟩
  rw [ha,map_one] at he
  have hh := congrArg (fun x : V => (x : G)) (s.marking.coordinates.injective he)
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

private theorem quotient_five_action {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    ∃ f : (H ⧸ pCore 2 H) →* Equiv.Perm (Fin 5), Function.Injective f ∧
      alternatingGroup (Fin 5) ≤ f.range := by
  obtain ⟨e⟩ := s.HStar_in_pointSupplement_residual_a5 h structural hH hHX
  let S := T.subtype hH.1.1.2
  have he := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    (pResidual 2 H) (S : Subgroup H) le_normalizer_of_normal S.isPGroup' e
  rw [pResidual_sup_sylow_eq_top S] at he
  let c := QuotientGroup.congr _ _ (topEquiv : (⊤ : Subgroup H) ≃* H)
    (pCore_map_iso 2 topEquiv)
  rcases he with ha | ha
  · obtain ⟨a⟩ := ha
    let d := c.symm.trans a
    refine ⟨(alternatingGroup (Fin 5)).subtype.comp d.toMonoidHom,
      Subtype.val_injective.comp d.injective,?_⟩
    intro x hx
    obtain ⟨y,hy⟩ := d.surjective ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · obtain ⟨a⟩ := ha
    let d := c.symm.trans a
    refine ⟨d.toMonoidHom,d.injective,?_⟩
    rw [MonoidHom.range_eq_top.mpr d.surjective]
    exact le_top

/-- The full H-action kernel, including elements outside the chosen Sylow. -/
theorem HStar_in_pointSupplement_action_kernel_le_core {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    H ⊓ centralizer (s.marking.UH H : Set G) ≤ H.pCoreIn 2 := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    change H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (Chapter3.Section02.localOrbit T L : Set G))
    simpa only [D.localOrbit_eq,ExteriorMarking.M] using hH
  have hP := Chapter10.source_hstar_minimal_parabolic_of_generation_gt_one F hH'
    ((s.exteriorFusion_from_source h structural).generation_gt_one H hH)
  let S := T.subtype hH.1.1.2
  obtain ⟨f,hf,hfA⟩ := s.quotient_five_action h structural hH hHX
  have hJQ : minimalParabolicCore S hP ≤ pCore 2 H := by
    let q := QuotientGroup.mk' (pCore 2 H)
    let I := minimalParabolicCoreImage S hP
    let : I.Normal := (inferInstance : (minimalParabolicCore S hP).Normal).map q
      (QuotientGroup.mk'_surjective _)
    let : Group.IsNilpotent I := minimalParabolic_coreImage_nilpotent S hP
    have hi := Theory.SpecificGroups.FivePointSylowParabolic.solvable_normal_le_ker f hfA I
    rw [(MonoidHom.ker_eq_bot_iff f).mpr hf] at hi
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact hi (mem_map_of_mem q hx)
  let C := (centralizer (s.marking.UH H : Set G)).subgroupOf H
  have hn : H ≤ normalizer (centralizer (s.marking.UH H : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _)
  let : C.Normal := normal_subgroupOf_iff_le_normalizer_inf.mpr
    ((le_inf hn H.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hKC : ¬ minimalParabolicResidual (H := H) ≤ C := by
    intro hc
    apply s.HStar_residual_not_centralizing_span h structural hH
    rintro x ⟨y,hy,rfl⟩
    exact hc hy
  have hCQ := (minimalParabolic_normal_le_core_of_residual_not_le S hP C hKC).trans hJQ
  intro x hx
  exact ⟨⟨x,hx.1⟩,hCQ hx.2,rfl⟩

/-- The same action kernel lies in the intrinsic core of the terminal join. -/
theorem HStar_in_pointSupplement_action_kernel_le_terminal_core {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    H ⊓ centralizer (s.marking.UH H : Set G) ≤ terminalCore s.marking H := by
  have hc := s.HStar_in_pointSupplement_action_kernel_le_core h structural hH hHX
  have hT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2) hy
  have hCTV : H ⊓ centralizer (s.marking.UH H : Set G) ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    le_inf (hc.trans hT) ((le_inf (hc.trans hT)
      (inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _)))).trans
        s.sylow_centralizer_seven_le_seed)
  exact (le_inf hc (hCTV.trans (s.sylow_centralizer_le_pointSupplement h))).trans
    (s.HStar_core_inf_supplement_le_terminal_core h structural
      (hHX.trans (sup_le s.pointSupplement_le_point s.sylow_le_G₁)))

/-- Construct the actual terminal data from the source point escape. -/
theorem terminalConfiguration_of_point_escape
    (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) :
    Nonempty (TerminalConfiguration s.marking) := by
  obtain ⟨H,hH,hHX,hHG⟩ := s.exists_HStar_in_pointSupplement h structural hout
  obtain ⟨g,hAT,_,hAC,hescape⟩ := s.exists_conjugate_escaping_HStar_core h structural hH
  have hcor := s.terminal_corank_le_two_in_pointSupplement h structural hH hHX hAT hAC
  have hcomm := s.terminal_commutator_line_of_point_parabolic_le h hHG
    (s.point_parabolic_le_residual_sup_HStar h structural hH hHX) g
  have hAH := hAT.trans hH.1.1.2
  let := s.HStar_span_elementary h structural hHG
  exact ⟨{
    H := H
    sylow_le := hH.1.1.2
    point_le := hHG
    g := g
    conjugate_le := hAH
    escapes_core := hescape
    span_two := IsElementaryAbelian.isPGroup 2 (s.marking.UH H)
    span_normalizes := s.terminal_span_normalizes_of_corank_two h structural hHG hAH hcomm hcor
    commutator_line := hcomm
    small_corank := s.terminal_corank_lt_globalS h structural hcor
    action_kernel := s.HStar_in_pointSupplement_action_kernel_le_terminal_core h structural hH hHX }⟩

/-- The terminal paragraph of 12.5.1; only the earlier point escape remains. -/
theorem exterior_false_of_point_escape
    (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) : False := by
  obtain ⟨d⟩ := s.terminalConfiguration_of_point_escape h structural hout
  exact s.exterior_contradiction_from_source_and_terminal h structural d

/-- Every surviving exterior marking must have its point group inside M.
Source 12.4.4 must still exclude this containment. -/
theorem point_group_le_M_from_terminal : s.marking.Gi 1 ≤ s.marking.M := by
  by_contra hout
  exact s.exterior_false_of_point_escape h structural hout

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
