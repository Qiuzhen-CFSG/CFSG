module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.MovedModule
public import Theory.GroupAction.FourPointResidual

/-!
# The original moved line stabilizer and moving plane

The T-invariant subgroup MZ centralizes both original exchanged lines, so the
proved seed-centralizer bound is an equality. The two-perfect cubic actor is
transitive on the nonidentity elements of its moving four-group. The original
exchanged line therefore generates that whole plane inside U, and full cubic
movement puts the plane in UL. These retain the source objects in 15.1.28--29.

Source: Aschbacher--Smith, printed pp.1103--1104.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- T-normality of MZ makes it centralize the literal exchanged line. -/
theorem MZ_le_centralizer_Z2 (d : CaseIComponentData T M Mc V) (s : d.NineSource)
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
theorem Z2_centralizer_eq_MZ (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.G1 ⊓ centralizer (d.Z2 t : Set G) = d.MZ :=
  le_antisymm (d.Z2_centralizer_le_MZ s hM hu h t ht htS)
    (le_inf inf_le_left (d.MZ_le_centralizer_Z2 s t ht))

/-- Restriction to the same component gives its exact distinguished parabolic. -/
theorem Z2_component_centralizer_eq_ML (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.L ⊓ centralizer (d.Z2 t : Set G) = d.ML := by
  apply le_antisymm
  · exact le_inf ((inf_le_inf_right _ d.L_component.1).trans
      (d.Z2_centralizer_le_MZ s hM hu h t ht htS)) inf_le_left
  · exact le_inf inf_le_right (inf_le_left.trans (d.MZ_le_centralizer_Z2 s t ht))

/-- The original moved line has precisely ML as its component stabilizer. -/
theorem Z2_moved_line_stabilizer (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ∃ ZU : Subgroup G, ZU ≤ d.UL t ∧ Nat.card ZU = 2 ∧
      ZU ≤ centralizer (d.S : Set G) ∧ d.L ⊓ centralizer (ZU : Set G) = d.ML := by
  obtain ⟨ZU,hU,hcard,hS,he,_⟩ := d.Z2_moved_line s hG hM hu h hi hf t ht htS
  exact ⟨ZU,hU,hcard,hS,he.trans (d.Z2_component_centralizer_eq_ML s hM hu h t ht htS)⟩

/-- The moving four-group lies in the span of the original exchanged line. -/
theorem nineMovingPlane_le_U (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.nineMovingPlane ≤ d.U t := by
  let := s.quasisimple
  let := h.elementary
  let W := d.nineMovingPlane
  let Y := d.nineCubic
  have hWV : W ≤ V := (show W ≤ d.nineFixedPlane ⊔ W from le_sup_right).trans_eq s.planes_sup
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  have hn : Y ≤ normalizer (W : Set G) := by
    change d.nineCubic ≤ normalizer (d.nineMovingPlane : Set G)
    rw [←s.cubic_moving]
    exact normalizer_commutator_ge_right _ _
  have hYL : Y ≤ d.L := by
    change (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤ d.L
    rw [(d.source_cubic_component hG h hf).2]
    exact (map_subtype_le _).trans inf_le_right
  let f : Y →* MulAut W := W.normalizerMonoidHom.comp (inclusion hn)
  have hZne : d.Z2 t ≠ ⊥ := by
    intro he
    exact d.Z1_ne_bot ((map_eq_bot_iff_of_injective d.Z1 (MulAut.conj t).injective).mp he)
  obtain ⟨z,hz,hzne⟩ := (d.Z2 t).bot_or_exists_ne_one.resolve_left hZne
  let x : W := ⟨z,d.Z2_le_movingPlane s t ht htS hz⟩
  have hx : x ≠ 1 := fun he => hzne (congrArg Subtype.val he)
  have hmove : ∃ a, f a x ≠ x := by
    by_contra hno
    push Not at hno
    have hf0 := MulAction.four_action_eq_one_of_twoPerfect_fixed s.cubic_two_perfect
      s.moving_card f x hx hno
    have hc : W ≤ centralizer (Y : Set G) := by
      intro w hw a ha
      have he := congrArg (fun k : Y →* MulAut W => (k ⟨a,ha⟩ ⟨w,hw⟩ : G)) hf0
      change a*w*a⁻¹ = w at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have he : W = ⊥ := s.cubic_moving.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hc)
    have hh := s.moving_card
    change Nat.card W = 4 at hh
    rw [he,card_bot] at hh
    norm_num at hh
  intro w hw
  by_cases hw1 : w = 1
  · exact hw1 ▸ (d.U t).one_mem
  obtain ⟨a,ha⟩ := MulAction.four_orbit_of_twoPerfect s.cubic_two_perfect
    s.moving_card f x hx hmove ⟨w,hw⟩ (fun he => hw1 (congrArg Subtype.val he))
  have he : (a : G)*z*(a : G)⁻¹ = w := congrArg Subtype.val ha
  exact he ▸ (le_normalizer_iff.mp (le_normalizer_conjugateSpanBy (d.Z2 t) d.L)
    a (hYL a.property) z (le_conjugateSpanBy _ _ hz))

/-- The original moving plane is contained in UL, as required in 15.1.29. -/
theorem nineMovingPlane_le_UL (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.nineMovingPlane ≤ d.UL t := by
  let := s.quasisimple
  have hYL : d.nineCubic ≤ d.L := by
    change (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤ d.L
    rw [(d.source_cubic_component hG h hf).2]
    exact (map_subtype_le _).trans inf_le_right
  exact s.cubic_moving.symm.le.trans
    (commutator_mono (d.nineMovingPlane_le_U s hG h hf t ht htS) hYL)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
