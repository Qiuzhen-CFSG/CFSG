module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.SourceInterface

/-!
# The exchanged seed for both surviving source rows

The seed lies in the omega-center of Q1 and is fixed by S. Its diagonal
with Z1 gives a central involution of T, forcing its component centralizer
to be the original ML. These arguments use neither the order-two marking
nor the order-four plane, and therefore also apply to source row (6).

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterA.Section05To06 Section03 Section03.InitialSource ChapterB
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem exchanged_Z2_le_omega_Q1 (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.Z2 t ≤ omegaOneCenterAmbient d.Q1 := by
  have he : d.Q1.map (MulAut.conj t).toMonoidHom = d.Q1 :=
    mem_normalizer_iff_map_conj_eq.mp (s.sylow_normalizes_Q1 ht)
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom) (d.Z1_le_omega_Q1 hM hu h)
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective, he] at hh
  exact hh

theorem exchanged_Z2_le_movingPlane (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.Z2 t ≤ d.nineMovingPlane := by
  exact (map_mono s.marked_le_fixed).trans_eq (s.exchanges t ht htS).1

theorem exchanged_Z2_le_centralizer_S (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
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

/-- The exchanged seed has the actual distinguished-centralizer bound. -/
theorem exchanged_Z2_centralizer_le_MZ (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
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
      (d.exchanged_Z2_le_movingPlane s t ht htS ha2)
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
      exact ⟨s.marked_le_fixed ha,haa ▸ d.exchanged_Z2_le_movingPlane s t ht htS ha2⟩
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

theorem exchanged_Z2_not_centralizes_L (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ¬ d.Z2 t ≤ centralizer (d.L : Set G) := by
  intro hc
  exact d.L_not_le_MZ ((le_inf d.L_component.1 (le_centralizer_iff.mp hc)).trans
    (d.exchanged_Z2_centralizer_le_MZ s hM hu h t ht htS))
/-- T-normality of MZ makes it centralize the literal exchanged seed. -/
theorem exchanged_MZ_le_centralizer_Z2 (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.MZ ≤ centralizer (d.Z2 t : Set G) := by
  intro x hx z hz
  obtain ⟨a,ha,rfl⟩ := hz
  have hxt : t⁻¹*x*t ∈ d.MZ := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (s.sylow_normalizes_MZ (T.inv_mem ht)) x).mp hx
  have he := congrArg (MulAut.conj t) (hxt.1 a ha)
  simpa [map_mul, MulAut.conj_apply, mul_assoc] using he

/-- The original distinguished centralizer is exactly MZ. -/
theorem exchanged_Z2_centralizer_eq_MZ (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.G1 ⊓ centralizer (d.Z2 t : Set G) = d.MZ :=
  le_antisymm (d.exchanged_Z2_centralizer_le_MZ s hM hu h t ht htS)
    (le_inf inf_le_left (d.exchanged_MZ_le_centralizer_Z2 s t ht))

/-- Restriction to the same component gives its exact distinguished centralizer. -/
theorem exchanged_Z2_component_centralizer_eq_ML (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.L ⊓ centralizer (d.Z2 t : Set G) = d.ML := by
  apply le_antisymm
  · exact le_inf ((inf_le_inf_right _ d.L_component.1).trans
      (d.exchanged_Z2_centralizer_le_MZ s hM hu h t ht htS)) inf_le_left
  · exact le_inf inf_le_right (inf_le_left.trans (d.exchanged_MZ_le_centralizer_Z2 s t ht))

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
