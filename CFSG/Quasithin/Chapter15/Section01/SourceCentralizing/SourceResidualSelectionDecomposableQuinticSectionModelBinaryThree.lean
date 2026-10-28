module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionModelHalf
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeOffender
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The original half-cost actor excludes the binary SL3 central cover

The natural quotient has ratio one-half, so the same original quadratic
actor is best on that quotient and belongs to its marked component. In the
literal binary SL3 cover, rank four is excluded by the group order 168.
A four-dimensional cover has every involution of fixed codimension two,
contradicting the remaining original rank-two, codimension-one cost.
The central projection is therefore injective and gives a whole-module
natural marking, with the original component and actor unchanged.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource

private theorem native_cover_injective_of_half_cost
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (τ : Representation (ZMod 2) BinaryLinearThree.Group W)
    (p : τ.IntertwiningMap BinaryLinearThree.W) (hp : IsCover p)
    {A : Subgroup BinaryLinearThree.Group} (hA : IsElementaryTwo A)
    (hcost : (rank A = 2 ∧ fixedCodim τ A = 1) ∨
      (rank A = 4 ∧ fixedCodim τ A = 2)) : Function.Injective p := by
  have hk := finrank_ker_le_H1_of_cover p hp
  rw [SLThreeCentralExtension.finrank_H1_dual] at hk
  have hd := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top, Module.finrank_fin_fun] at hd
  have hr4 : rank A ≠ 4 := by
    intro hr
    have hdiv := A.card_subgroup_dvd_card
    rw [hA.card_eq_two_pow_rank, hr, Matrix.PSL3Two.card_SL] at hdiv
    norm_num at hdiv
  have hc : fixedCodim τ A = 1 := by rcases hcost with h | h; exact h.2; exact (hr4 h.1).elim
  have hn4 : Module.finrank (ZMod 2) W ≠ 4 := by
    intro hd4
    let : IsElementaryAbelian 2 A := hA.2
    obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ho : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) hne
    have hi := BinaryLinearThree.NaturalExtension.involution_codim_of_commutator_top
      τ hd4 hp.2.2 a ho
    have hf : fixedSpace τ A ≤ fixedSpace τ (zpowers a) := by
      intro v hv b
      exact hv ⟨b, (zpowers_le.mpr ha) b.property⟩
    have hb := Submodule.finrank_mono hf
    have h₁ := fixedCodim_add_finrank τ A
    have h₂ := fixedCodim_add_finrank τ (zpowers a)
    omega
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A fully moved binary SL3 row with the actual half-cost actor has no
central attachment. The actor containment is derived from quotient bestness. -/
theorem binary_three_fixed_eq_bot_of_half_cost
    (σ : Representation (ZMod 2) G W) {A L : Subgroup G}
    (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hcost : (rank A = 2 ∧ fixedCodim σ A = 1) ∨
      (rank A = 4 ∧ fixedCodim σ A = 2))
    (s : MovedSection σ L) (hi : IsIrrPlus σ L s.space.toSubmodule)
    (hm : moved σ L = ⊤)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two 3))
    (hgen : offenderSubgroup s.action = L) (hratio : quadraticRatio s.action = 1 / 2) :
    A ≤ L ∧ fixedSpace σ L = ⊥ := by
  have hsTop : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  have hqs : IsQuadratic s.action A :=
    quadratic_of_equivariant_surjection s.space.toRepresentation s.action
      s.central.toSubmodule.mkQ s.central.toSubmodule.mkQ_surjective
      (fun _ _ => rfl) A (quadratic_subrepresentation σ s.space hq)
  have hbound : 2 * fixedCodim s.action A ≤ rank A := by
    have h₁ := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
    have h₂ := fixedCodim_subrepresentation_le σ s.space A
    change fixedCodim s.action A + _ ≤ _ at h₁
    rcases hcost with h | h <;> omega
  have hbest := SourceCompletion.bestOffender_of_half_bound s.action hratio.ge hA hqs
    (SourceCompletion.actionRatio_le_half_of_twice s.action hA hbound)
  have hAL : A ≤ L := hgen ▸ hbest.le_offenderSubgroup s.action
  let τ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hp := MovedSection.coverProjection_isCover s hi e
  let B := (A.subgroupOf L).map e.groupEquiv.toMonoidHom
  have hA₀ := (show IsOffender s.action A from ⟨hA, by omega⟩).subgroupOf s.action hAL
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 (A.subgroupOf L) := hA₀.1.2
    refine ⟨?_, IsElementaryAbelian.map e.groupEquiv.toMonoidHom⟩
    intro hb
    exact hA₀.1.1 (((A.subgroupOf L).map_eq_bot_iff_of_injective e.groupEquiv.injective).mp hb)
  have hrB : rank B = rank A := by
    rw [rank_map_injective _ e.groupEquiv.injective, rank_subgroupOf hAL]
  have hspace : fixedCodim s.space.toRepresentation A = fixedCodim σ A :=
    (fixedCodim_subrepresentation_eq_iff σ s.space A).mpr (by rw [hsTop, top_sup_eq])
  have hcB : fixedCodim τ B = fixedCodim σ A := by
    have he := fixedCodim_map_equivariant (s.space.toRepresentation.comp L.subtype) τ
      e.groupEquiv.toMonoidHom (LinearEquiv.refl (ZMod 2) s.space.toSubmodule)
      (fun g v => by
        change s.space.toRepresentation g v =
          s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv g)) v
        rw [e.groupEquiv.symm_apply_apply]) (A.subgroupOf L)
    rw [fixedCodim_subgroupOf s.space.toRepresentation hAL, hspace] at he
    exact he.symm
  have hcostB : (rank B = 2 ∧ fixedCodim τ B = 1) ∨
      (rank B = 4 ∧ fixedCodim τ B = 2) := by
    rw [hrB, hcB]
    exact hcost
  have hpI : Function.Injective p := native_cover_injective_of_half_cost τ p hp hB hcostB
  refine ⟨hAL, bot_unique fun v hv => ?_⟩
  let w : s.space.toSubmodule := ⟨v, hsTop ▸ Submodule.mem_top⟩
  have hw : w ∈ s.central.toSubmodule := by
    rw [s.central_eq]
    intro l
    exact Subtype.ext (hv l)
  have hpw : p w = 0 := by
    change e.linearEquiv (s.central.toSubmodule.mkQ w) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hw, map_zero]
  exact congrArg Subtype.val (hpI (hpw.trans (map_zero p).symm))

/-- The same component now has natural coordinates on the entire original module. -/
theorem binary_three_whole_action_of_half_cost
    (σ : Representation (ZMod 2) G W) {A L : Subgroup G}
    (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hcost : (rank A = 2 ∧ fixedCodim σ A = 1) ∨
      (rank A = 4 ∧ fixedCodim σ A = 2))
    (s : MovedSection σ L) (hi : IsIrrPlus σ L s.space.toSubmodule)
    (hm : moved σ L = ⊤)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two 3))
    (hgen : offenderSubgroup s.action = L) (hratio : quadraticRatio s.action = 1 / 2) :
    A ≤ L ∧ Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two 3)) := by
  obtain ⟨hAL, hz⟩ := binary_three_fixed_eq_bot_of_half_cost σ hA hq hcost s hi hm e hgen hratio
  let f := s.fullComponentActionEquiv hm hz
  exact ⟨hAL, ⟨⟨e.groupEquiv, f.linearEquiv.trans e.linearEquiv, fun g v =>
    (congrArg e.linearEquiv (f.intertwines g v)).trans (e.intertwines g (f.linearEquiv v))⟩⟩⟩

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
