module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneExchange
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Choice

/-!
# The exchange on the actual rank-one parabolics

The plane centralizer contains exactly three covers of the original point
Sylow. This follows from the full-flag lattice of the actual SL₅(2) image,
transported through its two-group kernel and the point-join inclusion.
Conjugation by the original t permutes these three subgroups and preserves
containment in M. Two distinct nodes in M therefore force the escaping
node to be unique and t-invariant. In particular, constructing a node Pc
in M moved by t supplies the source equality Pᵗ=P.

Parabolic.PointNode and Parabolic.NodeExchange construct Pc and discharge
its movement premise. The owner qt-d-10-nona5-point-constrained retains
both terminal contradictions and the earlier model reduction. This module
does not assert LinearFiveExclusionAt.

Source: Aschbacher--Smith, 10.2.9, printed p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
open BinaryLinear.FiveFlagGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Exactly three actual rank-one subgroups of G lie between the original
point Sylow and the plane centralizer. -/
theorem LinearFiveData.rankOne_card {c : Context D t v I} (m : LinearFiveData c) :
    Nat.card (RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) = 3 := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  obtain ⟨S,hS⟩ := c.join_sylow
  have hS' : (S : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  have hSC : pointSylow T v ≤ C := le_inf le_sup_right m.pointSylow_centralizes_plane
  have hSC' : (S : Subgroup H) ≤ C.subgroupOf H := by
    rw [hS']
    exact comap_mono hSC
  have hc := rankOneBelow_card_of_two_kernel m.joinAction m.joinAction_surjective
    m.joinAction_kernel_two S (C.subgroupOf H) hSC' m.plane_maximal
  have he := Nat.card_congr (rankOneBelowEquivSubtype H (pointSylow T v) C hSC inf_le_left)
  rw [←hS'] at he
  exact he.symm.trans hc

private theorem LinearFiveData.exchange_rankOne_map {c : Context D t v I}
    (m : LinearFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
    pointSylow T v ⋖ P.val.map (MulAut.conj t).toMonoidHom ∧
      P.val.map (MulAut.conj t).toMonoidHom ≤ planeCentralizer T t v I := by
  have hS : (pointSylow T v).map (MulAut.conj t).toMonoidHom = pointSylow T v :=
    mem_normalizer_iff_map_conj_eq.mp (m.pointSylow_normalized c.escaping.t_mem)
  have hC : (planeCentralizer T t v I).map (MulAut.conj t).toMonoidHom =
      planeCentralizer T t v I :=
    mem_normalizer_iff_map_conj_eq.mp m.exchange_normalizes_plane_centralizer
  constructor
  · have hh := (apply_covBy_apply_iff (MulAut.conj t).mapSubgroup).mpr P.property.1
    change (pointSylow T v).map (MulAut.conj t).toMonoidHom ⋖
      P.val.map (MulAut.conj t).toMonoidHom at hh
    rwa [hS] at hh
  · exact (map_mono P.property.2).trans_eq hC

private theorem LinearFiveData.exchange_rankOne_square {c : Context D t v I}
    (m : LinearFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
    (P.val.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = P.val := by
  have hhom : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t ^ 2)).toMonoidHom := by
    ext x
    change t * (t * x * t⁻¹) * t⁻¹ = t ^ 2 * x * (t ^ 2)⁻¹
    simp only [pow_two]
    group
  rw [map_map,hhom]
  exact mem_normalizer_iff_map_conj_eq.mp (P.val.le_normalizer
    (P.property.1.le m.exchange_square_mem))

/-- The original element t acts as an involution on the three actual
rank-one nodes. Its square lies in C_T(v), so fixes every Sylow overgroup. -/
def LinearFiveData.rankOneExchange {c : Context D t v I} (m : LinearFiveData c) :
    RankOneBelow (pointSylow T v) (planeCentralizer T t v I) ≃
      RankOneBelow (pointSylow T v) (planeCentralizer T t v I) :=
  { toFun P := ⟨P.val.map (MulAut.conj t).toMonoidHom,
      by exact m.exchange_rankOne_map P⟩
    invFun P := ⟨P.val.map (MulAut.conj t).toMonoidHom,
      by exact m.exchange_rankOne_map P⟩
    left_inv P := by exact Subtype.ext (m.exchange_rankOne_square P)
    right_inv P := by exact Subtype.ext (m.exchange_rankOne_square P) }

@[simp] theorem LinearFiveData.rankOneExchange_apply_val {c : Context D t v I}
    (m : LinearFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
    (m.rankOneExchange P).val = P.val.map (MulAut.conj t).toMonoidHom := rfl

/-- The exchange also preserves which of these original subgroups lie in M. -/
theorem LinearFiveData.rankOneExchange_le_maximalLocal_iff {c : Context D t v I}
    (m : LinearFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
    (m.rankOneExchange P).val ≤ D.maximalLocal ↔ P.val ≤ D.maximalLocal := by
  have hM : D.maximalLocal.map (MulAut.conj t).toMonoidHom = D.maximalLocal :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer
      (le_normalizer_componentOrbit L T c.escaping.t_mem))
  change P.val.map (MulAut.conj t).toMonoidHom ≤ D.maximalLocal ↔ _
  conv_lhs => rw [←hM]
  exact map_le_map_iff_of_injective (MulAut.conj t).injective

/-- Once two distinct internal source nodes are identified in M, the third
node is the unique rank-one parabolic escaping M. -/
theorem LinearFiveData.exists_unique_escaping_rankOne_of_pair {c : Context D t v I}
    (m : LinearFiveData c)
    (A B : RankOneBelow (pointSylow T v) (planeCentralizer T t v I))
    (hAB : A ≠ B) (hAM : A.val ≤ D.maximalLocal) (hBM : B.val ≤ D.maximalLocal) :
    ∃! P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I),
      ¬ P.val ≤ D.maximalLocal := by
  apply existsUnique_rankOne_escaping_of_pair _ _ D.maximalLocal m.rankOne_card A B hAB hAM hBM
  obtain ⟨P,hP,hPC,hPM,_⟩ := m.exists_escaping_rankOne
  exact ⟨⟨P,hP,hPC⟩,hPM⟩

/-- The escaping source parabolic is normalized by the original t; this
uses the three-node lattice, preservation of M, and the two internal nodes. -/
theorem LinearFiveData.exchange_fixes_escaping_rankOne_of_pair {c : Context D t v I}
    (m : LinearFiveData c)
    (A B : RankOneBelow (pointSylow T v) (planeCentralizer T t v I))
    (hAB : A ≠ B) (hAM : A.val ≤ D.maximalLocal) (hBM : B.val ≤ D.maximalLocal)
    (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I))
    (hPM : ¬ P.val ≤ D.maximalLocal) :
    P.val.map (MulAut.conj t).toMonoidHom = P.val := by
  obtain ⟨Q,_,hunique⟩ := m.exists_unique_escaping_rankOne_of_pair A B hAB hAM hBM
  have hP := hunique P hPM
  have hPt := hunique (m.rankOneExchange P)
    ((m.rankOneExchange_le_maximalLocal_iff P).not.mpr hPM)
  exact congrArg Subtype.val (hPt.trans hP.symm)

/-- It suffices to construct the actual Pc in M and show that t moves it:
its conjugate supplies the second internal node, and the escaping node is
then t-invariant. This is the source P^t=P step with literal subgroups. -/
theorem LinearFiveData.exists_exchange_fixed_escaping_rankOne_of_moved_node
    {c : Context D t v I} (m : LinearFiveData c)
    (Pc : RankOneBelow (pointSylow T v) (planeCentralizer T t v I))
    (hPcM : Pc.val ≤ D.maximalLocal) (hmoved : m.rankOneExchange Pc ≠ Pc) :
    ∃ P : Subgroup G, pointSylow T v ⋖ P ∧ P ≤ planeCentralizer T t v I ∧
      ¬ P ≤ D.maximalLocal ∧ t ∈ normalizer (P : Set G) ∧
      Chapter1.IsSylowIn 2 (pointSylow T v) P := by
  obtain ⟨P,hP,hPC,hPM,hSyl⟩ := m.exists_escaping_rankOne
  let node : RankOneBelow (pointSylow T v) (planeCentralizer T t v I) := ⟨P,hP,hPC⟩
  refine ⟨P,hP,hPC,hPM,?_,hSyl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact m.exchange_fixes_escaping_rankOne_of_pair Pc (m.rankOneExchange Pc) hmoved.symm
    hPcM ((m.rankOneExchange_le_maximalLocal_iff Pc).mpr hPcM) node hPM

/-- Each actual rank-one node is a genuine minimal parabolic in the original
point join; its prescribed Sylow is not relatively normal. -/
theorem LinearFiveData.rankOne_isMinimalParabolic {c : Context D t v I}
    (m : LinearFiveData c)
    (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
    ∃ S : Sylow 2 (pointJoin T v I),
      (S : Subgroup _).map (pointJoin T v I).subtype = pointSylow T v ∧
      ChapterB.IsMinimalParabolicOver S (P.val.subgroupOf (pointJoin T v I)) := by
  let H := pointJoin T v I
  obtain ⟨S,hS⟩ := c.join_sylow
  have hPH : P.val ≤ H := P.property.2.trans inf_le_left
  have hcov : (S : Subgroup H) ⋖ P.val.subgroupOf H := by
    apply (covBy_map_subtype_iff H _ _).mp
    rw [hS,map_subgroupOf_eq_of_le hPH]
    exact P.property.1
  refine ⟨S,hS,(ChapterB.isMinimalParabolicOver_iff S _).mpr ⟨?_,?_⟩⟩
  · refine ⟨hcov.lt,⟨(S : Subgroup H),⟨le_rfl,hcov⟩,?_⟩⟩
    intro X hX
    exact ((covBy_iff_lt_and_eq_or_eq.mp hcov).2 X hX.1 hX.2.le).resolve_right hX.2.ne
  · intro hn
    have hnorm := (normal_subgroupOf_iff_le_normalizer hcov.le).mp hn
    rw [normalizer_sylow_eq_of_two_kernel m.joinAction m.joinAction_surjective
      m.joinAction_kernel_two S] at hnorm
    exact hcov.lt.not_ge hnorm

/-- Consumer of the cover and exchange results: the escaping minimal
parabolic in the literal point join has t-invariant ambient image. The
source Pc construction is the remaining premise of this exchange step. -/
theorem LinearFiveData.exists_exchange_fixed_minimalParabolic_of_moved_node
    {c : Context D t v I} (m : LinearFiveData c)
    (Pc : RankOneBelow (pointSylow T v) (planeCentralizer T t v I))
    (hPcM : Pc.val ≤ D.maximalLocal) (hmoved : m.rankOneExchange Pc ≠ Pc) :
    ∃ (S : Sylow 2 (pointJoin T v I)) (P : Subgroup (pointJoin T v I)),
      (S : Subgroup _).map (pointJoin T v I).subtype = pointSylow T v ∧
      ChapterB.IsMinimalParabolicOver S P ∧
      P.map (pointJoin T v I).subtype ≤ planeCentralizer T t v I ∧
      ¬ P.map (pointJoin T v I).subtype ≤ D.maximalLocal ∧
      t ∈ normalizer (P.map (pointJoin T v I).subtype : Set G) := by
  obtain ⟨P,hP,hPC,hPM,ht,_⟩ :=
    m.exists_exchange_fixed_escaping_rankOne_of_moved_node Pc hPcM hmoved
  obtain ⟨S,hS,hmin⟩ := m.rankOne_isMinimalParabolic ⟨P,hP,hPC⟩
  refine ⟨S,P.subgroupOf (pointJoin T v I),hS,hmin,?_,?_,?_⟩
  all_goals rwa [map_subgroupOf_eq_of_le (hPC.trans inf_le_left)]

end CFSG.Quasithin.Chapter10.PointControl.Constrained

