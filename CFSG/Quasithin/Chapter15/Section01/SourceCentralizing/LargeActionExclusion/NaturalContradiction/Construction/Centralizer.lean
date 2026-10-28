module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.RankTwo
public import Theory.GroupTheory.IndexTwoOmegaSpan

/-!
# The full Sylow omega-center and the adjacent parabolic

The index-two exchange and the source seed bound identify Ω₁Z(S) with
Z₁Z₂. Thus its centralizer in G₁ is M_Z. The adjacent parabolic has
prime index seven in KS; the first node escapes M_L S, so its intersection
with KS is exactly P₂. This identifies both the literal centralizer and
its two-core as required by C.1.34, without replacing Ω₁Z(S) by the smaller
original diagonal seed.

Source: Aschbacher--Smith 15.1.29, printed pp.1103--1104.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The full source hypotheses identify the entire Sylow omega-center,
not just the original diagonal central involution. -/
theorem omegaCenter_eq_exchanged_lines (d : CaseIComponentData T M Mc V)
    (hM : IsOrderingMaximal T M) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M) (s : d.ExchangedSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    SourceInterface.omegaCenterIn d.S = d.Z1 ⊔ d.Z2 t := by
  let := h.elementary
  have hZT : d.Z1 ≤ (T : Subgroup G) := by
    intro z hz
    exact ChapterB.thompsonJ_le _ _ ((mem_omegaOneCenterAmbient_iff _ _).mp
      (h.thompsonFixed_le_omega T hM (d.Z1_le_fixed hz))).1
  have hA : d.Z1 ≤ omegaOneCenterAmbient d.S := by
    intro a ha
    have hZV := d.Z1_le_fixed.trans inf_le_left
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨⟨hZT ha,fun z hz => (V.le_centralizer (hZV ha)) z (hZV hz)⟩,
        elemPow_eq_one_of_isElementaryAbelian a (hZV ha),
        fun x hx => (hx.2 a ha).symm⟩
  have hdis : d.Z1 ⊓ d.Z2 t = ⊥ := by
    apply le_bot_iff.mp
    rw [←s.planes_inf]
    exact inf_le_inf s.marked_le_fixed (d.exchanged_Z2_le_movingPlane s t ht htS)
  have he := Subgroup.omegaCenter_eq_exchanged_pair d.S (T : Subgroup G) d.Z1
    d.S_le_T s.index t ht htS hA hdis
    (d.centralInvolutions_le_exchanged_lines h hfull s t ht htS)
  have hω : SourceInterface.omegaCenterIn d.S = omegaOneCenterAmbient d.S := by
    rfl
  exact hω.trans he

/-- Inside G₁, both the full Sylow omega-center and the exchanged seed
have exactly the original distinguished centralizer M_Z. -/
theorem omegaCenter_centralizer_eq_MZ (d : CaseIComponentData T M Mc V)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (s : d.ExchangedSource) (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.G1 ⊓ centralizer (SourceInterface.omegaCenterIn d.S : Set G) = d.MZ := by
  rw [d.omegaCenter_eq_exchanged_lines hM h hfull s t ht htS]
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le (show d.Z2 t ≤ d.Z1 ⊔ d.Z2 t from le_sup_right))).trans
      (d.exchanged_Z2_centralizer_eq_MZ s hM hu h t ht htS).le
  · apply le_inf inf_le_left
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (show d.MZ ≤ centralizer (d.Z1 : Set G) from inf_le_left))
      (le_centralizer_iff.mp (d.exchanged_MZ_le_centralizer_Z2 s t ht))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The adjacent source parabolic is the exact intersection with M_L S.
Its index seven makes it maximal in KS, and the first node escapes M_L S. -/
theorem second_eq_pair_inf_marked (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hnat : d.HasNaturalMovedModule t) :
    a.parabolics.P2 = (a.parabolics.K ⊔ a.parabolics.Q2) ⊓ (d.ML ⊔ d.S) := by
  let J := a.parabolics.K ⊔ a.parabolics.Q2
  let C := J ⊓ (d.ML ⊔ d.S)
  have hPC : a.parabolics.P2 ≤ C := le_inf (a.second_lt_pair_radical hs.1).le
    (a.node_le_markedParabolic hG h hs hnat ⟨1,by have := a.dimension; omega⟩ (by simp))
  have hidx : a.parabolics.P2.relIndex J = 7 := a.second_index hs.1
  have hm := relIndex_mul_relIndex a.parabolics.P2 C J hPC inf_le_left
  have hp : (a.parabolics.P2.relIndex C * C.relIndex J).Prime :=
    hm ▸ (hidx ▸ (by decide : Nat.Prime 7))
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hc⟩ | ⟨_,hc⟩
  · have hJC : J ≤ C := relIndex_eq_one.mp hc
    have h0 : a.parabolics.P0 ≤ J := by
      change a.parabolics.P0 ≤ a.parabolics.K ⊔ a.parabolics.Q2
      rw [a.pair_radical_eq_sylow_join hs.1,a.pair_sylow_eq_nodes hs.1]
      exact le_sup_left
    exact (a.first_not_le_markedParabolic hnat (h0.trans (hJC.trans inf_le_right))).elim
  · exact le_antisymm hPC (relIndex_eq_one.mp hc)

/-- The C.1.34 centralizer marking is the literal adjacent parabolic. -/
theorem second_eq_omegaCenter_centralizer (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    a.parabolics.P2 = (a.parabolics.K ⊔ a.parabolics.Q2) ⊓
      centralizer (SourceInterface.omegaCenterIn d.S : Set G) := by
  let J := a.parabolics.K ⊔ a.parabolics.Q2
  have hJ : J ≤ d.L ⊔ d.S := by
    rw [show J = a.parabolics.K ⊔ d.S from a.pair_radical_eq_sylow_join hs.1]
    exact sup_le a.pair_le le_sup_right
  have hJG : J ≤ d.G1 := hJ.trans (sup_le d.L_component.1 d.S_le_G1)
  have hC : J ⊓ centralizer (SourceInterface.omegaCenterIn d.S : Set G) = J ⊓ d.MZ := by
    rw [←d.omegaCenter_centralizer_eq_MZ hM hu h hfull hs.1 t ht htS,
      ←inf_assoc,inf_eq_left.mpr hJG]
  have hMLZ : (d.L ⊔ d.S) ⊓ d.MZ = d.ML ⊔ d.S := by
    have he := a.marked_point_centralizer hG h hs (d.Z2 t)
      (d.exchanged_Z2_le_centralizer_S hs.1 t ht)
      (d.exchanged_Z2_component_centralizer_eq_ML hs.1 hM hu h t ht htS)
    rw [←d.exchanged_Z2_centralizer_eq_MZ hs.1 hM hu h t ht htS,←inf_assoc,
      show (d.L ⊔ d.S) ⊓ d.G1 = d.L ⊔ d.S from
        inf_eq_left.mpr (sup_le d.L_component.1 d.S_le_G1)]
    exact he
  rw [a.second_eq_pair_inf_marked hG h hs hnat,hC,←hMLZ,←inf_assoc,inf_eq_left.mpr hJ]


/-- The actual adjacent two-core supplies the omega-center core field. -/
theorem second_core_eq_omegaCenter_core (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    a.parabolics.Q2 = ((a.parabolics.K ⊔ a.parabolics.Q2) ⊓
      centralizer (SourceInterface.omegaCenterIn d.S : Set G)).pCoreIn 2 :=
  congrArg (fun P : Subgroup G => P.pCoreIn 2)
    (a.second_eq_omegaCenter_centralizer hG hM hu h hfull hs ht htS hnat)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
