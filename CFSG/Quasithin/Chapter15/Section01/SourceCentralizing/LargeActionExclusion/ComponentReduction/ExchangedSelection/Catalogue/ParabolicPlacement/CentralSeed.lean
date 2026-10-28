module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.CentralizerReduction

/-!
# The central seed in the literal component quotient

Once the original central involutions normalize the selected component,
their nontrivial image is contained in the omega center of N_S(L)'s image.
The singleton centralizer overgroup and L outside M_Z give nontriviality.
Thus the order-two model premise identifies Z⁺ with Z_L⁺.

The normalization input is retained explicitly: centralizing S alone is
not being substituted for normalizing L. Source: Aschbacher--Smith,
original 15.1.22(**), printed p.1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem marked_le_sylow (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M) :
    d.Z1 ≤ (T : Subgroup G) := by
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  exact (d.Z1_le_fixed.trans inf_le_left).trans hVT

theorem central_seed_le_sylowNormalizer (d : CaseIComponentData T M Mc V)
    (hZ1T : d.Z1 ≤ (T : Subgroup G))
    (hn : centralInvolutions T ≤ normalizer (d.L : Set G)) :
    centralInvolutions T ≤ d.sylowNormalizer := by
  intro z hz
  exact ⟨⟨centralInvolutions_le_sylow T hz,
    centralizer_le hZ1T (centralInvolutions_le_centralizer_sylow T hz)⟩, hn hz⟩

theorem central_seed_plus_le_omega (d : CaseIComponentData T M Mc V)
    (hZ1T : d.Z1 ≤ (T : Subgroup G))
    (hn : centralInvolutions T ≤ normalizer (d.L : Set G)) :
    d.plus (centralInvolutions T) ≤ d.plusOmega := by
  rintro _ ⟨z,hz,rfl⟩
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨mem_map_of_mem _ (d.central_seed_le_sylowNormalizer hZ1T hn hz), ?_, ?_⟩
  · have hz2 : (z : G)^2 = 1 :=
      (mem_omegaCenterIn_iff (T : Subgroup G) _).mp hz |>.2.2
    rw [←map_pow, show z^2=1 from Subtype.ext hz2, map_one]
  · rintro _ ⟨a,ha,rfl⟩
    exact congrArg d.plusMap (Subtype.ext
      (centralInvolutions_le_centralizer_sylow T hz a (d.S_le_T ha.1)))

theorem central_seed_plus_ne_bot (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hZ1T : d.Z1 ≤ (T : Subgroup G))
    (hn : centralInvolutions T ≤ normalizer (d.L : Set G)) :
    d.plus (centralInvolutions T) ≠ ⊥ := by
  intro he
  have hc := (d.plus_eq_bot_iff _ ((d.central_seed_le_sylowNormalizer hZ1T hn).trans
    d.sylowNormalizer_le_componentNormalizer)).mp he
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  exact d.L_not_le_Mc ((le_centralizer_iff.mp hc).trans hMc.2)

/-- The first equality of (**) on the original pre-exclusion component,
with only central-involution normalization retained as an earlier input. -/
theorem central_seed_plus_eq_omega (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hn : centralInvolutions T ≤ normalizer (d.L : Set G))
    (hcard : Nat.card d.plusOmega = 2) :
    d.plus (centralInvolutions T) = d.plusOmega := by
  have hZ1T := d.marked_le_sylow h hTM
  apply eq_of_le_of_card_ge (d.central_seed_plus_le_omega hZ1T hn)
  rw [hcard]
  exact Nat.succ_le_of_lt ((one_lt_card_iff_ne_bot _).mpr
    (d.central_seed_plus_ne_bot hu hZ1T hn))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
