module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Selection
public import Theory.GroupTheory.IndexTwoOmegaDiagonal
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.PGroup.OmegaCenterIn
/-!
# The original exchanged line and its distinguished centralizer

The same t in T\S sends Z1 into the moving plane and the omega-center of Q1.
Its diagonal product with Z1 is a nontrivial central involution of T, giving
C_G1(Z2) <= MZ and nontrivial L-action on the actual exchanged line.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
@[expose] def Z2 (d : CaseIComponentData T M Mc V) (t : G) : Subgroup G :=
  d.Z1.map (MulAut.conj t).toMonoidHom
@[expose] def U (d : CaseIComponentData T M Mc V) (t : G) : Subgroup G :=
  conjugateSpanBy (d.Z2 t) d.L
@[expose] def UL (d : CaseIComponentData T M Mc V) (t : G) : Subgroup G :=
  ⁅d.U t,d.L⁆

theorem Z1_le_omega_Q1 (d : CaseIComponentData T M Mc V)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) : d.Z1 ≤ omegaOneCenterAmbient d.Q1 := by
  let := h.elementary
  have hZV := d.Z1_le_fixed.trans inf_le_left
  have hZT : d.Z1 ≤ (T : Subgroup G) := by
    intro z hz
    exact thompsonJ_le _ _ ((mem_omegaOneCenterAmbient_iff _ _).mp
      (h.thompsonFixed_le_omega T hM (d.Z1_le_fixed hz))).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hZZ : d.Z1 ≤ centralizer (d.Z1 : Set G) :=
    hZV.trans (V.le_centralizer.trans (centralizer_le hZV))
  have hZQ : d.Z1 ≤ d.Q1 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le hZV)
    (le_inf hZZ (hZT.trans hTMc))
    (inf_le_left.trans (Subgroup.centralizer_le_normalizer _))
  intro z hz
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hZQ hz,
    elemPow_eq_one_of_isElementaryAbelian z (hZV hz),
    fun q hq => ((d.Q1_le_MZ.trans inf_le_left) hq z hz).symm⟩

theorem Z2_le_omega_Q1 (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.Z2 t ≤ omegaOneCenterAmbient d.Q1 := by
  have he : d.Q1.map (MulAut.conj t).toMonoidHom = d.Q1 :=
    mem_normalizer_iff_map_conj_eq.mp (s.sylow_normalizes_Q1 ht)
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom) (d.Z1_le_omega_Q1 hM hu h)
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective, he] at hh
  exact hh

theorem Z2_le_movingPlane (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.Z2 t ≤ d.nineMovingPlane := by
  exact (map_mono s.marked_le_fixed).trans_eq (s.exchanges t ht htS).1

theorem Z2_le_centralizer_S (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) : d.Z2 t ≤ centralizer (d.S : Set G) := by
  have hSn : (T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.S_le_T).mp s.sylow_normal
  rintro z ⟨a,ha,rfl⟩ x hx
  have hxt : t⁻¹*x*t ∈ d.S := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (hSn (T.inv_mem ht)) x).mp hx
  have he := hxt.2 a ha
  change x*(t*a*t⁻¹) = (t*a*t⁻¹)*x
  calc
    x*(t*a*t⁻¹) = t*((t⁻¹*x*t)*a)*t⁻¹ := by group
    _ = t*(a*(t⁻¹*x*t))*t⁻¹ := by rw [he.symm]
    _ = (t*a*t⁻¹)*x := by group

/-- The exchanged line has the actual distinguished-centralizer bound. -/
theorem Z2_centralizer_le_MZ (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.G1 ⊓ centralizer (d.Z2 t : Set G) ≤ d.MZ := by
  let := h.elementary
  have hZV := d.Z1_le_fixed.trans inf_le_left
  obtain ⟨a,ha,hane⟩ := d.Z1.bot_or_exists_ne_one.resolve_left d.Z1_ne_bot
  have hZT : d.Z1 ≤ (T : Subgroup G) := by
    intro z hz
    exact thompsonJ_le _ _ ((mem_omegaOneCenterAmbient_iff _ _).mp
      (h.thompsonFixed_le_omega T hM (d.Z1_le_fixed hz))).1
  have haS : a ∈ d.S := ⟨hZT ha,fun z hz =>
    (V.le_centralizer (hZV ha)) z (hZV hz)⟩
  have haOm : a ∈ omegaOneCenterAmbient d.S :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨haS,elemPow_eq_one_of_isElementaryAbelian a (hZV ha),fun x hx => (hx.2 a ha).symm⟩
  have ha2 : t*a*t⁻¹ ∈ d.Z2 t := mem_map_of_mem (MulAut.conj t).toMonoidHom ha
  have ha2V : t*a*t⁻¹ ∈ V :=
    (show d.nineMovingPlane ≤ V from (show d.nineMovingPlane ≤ d.nineFixedPlane ⊔ d.nineMovingPlane from le_sup_right).trans_eq s.planes_sup)
      (d.Z2_le_movingPlane s t ht htS ha2)
  have hz := indexTwo_diagonal_mem_omegaCenter d.S (T : Subgroup G) d.S_le_T s.index t ht htS a haOm
    (V.le_centralizer (hZV ha) _ ha2V).symm
  have hzne : a*(t*a*t⁻¹) ≠ 1 := by
    intro he
    have haa : t*a*t⁻¹ = a := by
      have ha2pow := elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hZV ha)
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha2pow)
      exact (eq_inv_of_mul_eq_one_right he).trans hai
    have habot : a ∈ (⊥ : Subgroup G) := by
      rw [←s.planes_inf]
      exact ⟨s.marked_le_fixed ha,haa ▸ d.Z2_le_movingPlane s t ht htS ha2⟩
    exact hane (mem_bot.mp habot)
  have hbound := central_involution_centralizer_le_partner T hu hz hzne
  intro x hx
  refine ⟨hx.1,hbound ?_⟩
  rw [mem_centralizer_singleton_iff]
  have hxa := hx.1 a ha
  have hxb := hx.2 (t*a*t⁻¹) ha2
  calc
    x*(a*(t*a*t⁻¹)) = (x*a)*(t*a*t⁻¹) := by group
    _ = (a*x)*(t*a*t⁻¹) := by rw [hxa.symm]
    _ = a*((t*a*t⁻¹)*x) := by rw [mul_assoc,hxb.symm]
    _ = (a*(t*a*t⁻¹))*x := by group

theorem Z2_not_centralizes_L (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ¬ d.Z2 t ≤ centralizer (d.L : Set G) := by
  intro hc
  exact d.L_not_le_MZ ((le_inf d.L_component.1 (le_centralizer_iff.mp hc)).trans
    (d.Z2_centralizer_le_MZ s hM hu h t ht htS))
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
