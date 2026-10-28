module
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.FirstTwoCore
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.TwoMovedLayers
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.Centralizer

/-!
# The two-layer nonblock step for the natural parabolic

The actual first-pair action has a noncentral two-core. Its kernel kills the
moved two-layer in the source residual, while the source short-layer
alternative would force that layer into the kernel. The resulting quotient
contradiction proves the adjacent pair is not a C.1.34 linear block.

Source: Aschbacher--Smith 15.1.29, printed pp.1103--1104.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
open CFSG.Quasithin.ChapterA.Section05To06 CFSG.Quasithin.Chapter15.Section03
open Theory.SpecificGroups.BinaryComponentResidual
open BinaryLinear.OrderedResidualConjugators
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The literal image of K is the join of the same two marked node residuals. -/
theorem pair_action_range (a : NaturalFlag d t) :
    (a.action.comp (inclusion a.pair_le)).range =
      nodeResidual a.basis ⟨0,by have := a.dimension; omega⟩ ⊔
      nodeResidual a.basis ⟨1,by have := a.dimension; omega⟩ := by
  have he : (a.action.comp (inclusion a.pair_le)).range =
      (a.parabolics.K.subgroupOf (d.L ⊔ d.S)).map a.action := by
    ext g
    constructor
    · rintro ⟨k,rfl⟩
      exact mem_map_of_mem a.action k.property
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
  have h0 : a.parabolics.Y0 ≤ d.L ⊔ d.S := (map_subtype_le _).trans a.parabolics_le.1
  have h2 : a.parabolics.Y2 ≤ d.L ⊔ d.S := (map_subtype_le _).trans a.parabolics_le.2.1
  rw [he,NaturalParabolics.K,subgroupOf_sup h0 h2,Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (a.node_residual_image _) (a.node_residual_image _)

/-- Movement below the natural-action kernel and in its quotient
rules out a single short layer, hence the SL₃(2) block. -/
theorem pair_not_linear_block (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    ¬ ChapterC.IsSL3EvenBlock a.parabolics.K 1 := by
  let := a.elementary
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model (small_binary_model_of_marking hn e)
  let hi := s.c27Input hG h hf hs.2.1
  have hUS : d.UL t ≤ d.S := (d.UL_le_U t).trans
    ((d.U_le_Q1 s hG hM hu h hi hf t ht).trans (d.Q1_le_S s hu))
  have hKU := a.pair_le.trans a.normalizes
  have hUK := hUS.trans a.sylow_normalizes_pair
  have hW := d.nineMovingPlane_le_UL s hG h hf t ht htS
  have hmove : ¬ d.UL t ≤ centralizer (a.parabolics.K : Set G) := by
    intro hc
    have hz : ⁅d.nineMovingPlane,a.parabolics.Y0⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        ((hW.trans hc).trans (centralizer_le (show a.parabolics.Y0 ≤ a.parabolics.K from le_sup_left)))
    rw [a.first_moves_movingPlane hG hM hu h hs ht htS hnat] at hz
    have hh := s.moving_card
    rw [hz,card_bot] at hh
    omega
  let f := a.action.comp (inclusion a.pair_le)
  have hkernel : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hk : IsPGroup 2 a.action.ker := by
      rw [show a.action.ker = pCore 2 (d.L ⊔ d.S : Subgroup G) from a.kernel]
      exact pCore_isPGroup
    exact hk.comap_of_injective _ (inclusion_injective a.pair_le)
  have hkill : ∀ x : a.parabolics.K, (x : G) ∈ d.UL t → f.rangeRestrict x = 1 := by
    intro x hx
    apply Subtype.ext
    change a.action (inclusion a.pair_le x) = 1
    apply MonoidHom.mem_ker.mp
    change inclusion a.pair_le x ∈ (naturalAction _ _ _ _).ker
    rw [naturalAction_ker]
    exact (d.UL t).le_centralizer hx
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hupper : ¬ pCore 2 f.range ≤ center f.range := by
    change ¬ pCore 2 (a.action.comp (inclusion a.pair_le)).range ≤
      center (a.action.comp (inclusion a.pair_le)).range
    rw [a.pair_action_range]
    exact first_two_core_not_central (by have := a.dimension; omega) a.basis
  intro hb
  exact ChapterC.not_short_of_two_moved_layers a.parabolics.K (d.UL t)
    (IsElementaryAbelian.isPGroup 2 _) hKU hUK hmove f.rangeRestrict
    f.rangeRestrict_surjective hkernel hkill hupper hb.2.1
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
