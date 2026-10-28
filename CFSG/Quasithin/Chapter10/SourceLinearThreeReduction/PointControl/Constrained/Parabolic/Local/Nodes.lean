module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Local.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.NodeExchange

/-!
# The exchanged local point nodes and the escaping parabolic

The local natural-three coordinates give C_L(u) index seven. Adjoining
the point Sylow gives a rank-one node Pc of index three. Its conjugate
has two-group action on the local three-space, so it differs from Pc.
The three-node lattice of the actual plane parabolic then fixes its
unique node outside M under the original exchanger.

This adapts the existing Choice, Exchange, PointNode and NodeExchange
proofs using only the local natural copy and the smaller faithful orbit.
All relative normality and Sylow inclusions refer to the original join.
Source: Aschbacher--Smith, 10.2.9, p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
open BinaryLinear.FiveFlagGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}


/-- The original natural component moves the opposite involution. -/
theorem LocalFiveData.component_not_le_plane_centralizer {c : Context D t v I}
    (m : LocalFiveData c) : ¬ L ≤ planeCentralizer T t v I := by
  intro hL
  have hu : oppositePoint t v ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G) := by
    refine ⟨m.opposite_mem_moved,?_⟩
    intro l hl
    have hh := hL hl
    change l ∈ pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) at hh
    rw [c.join_plane_centralizer] at hh
    exact mem_centralizer_singleton_iff.mp hh.2
  rw [m.moved_fixed_eq_bot] at hu
  exact c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp hu)

/-- The original component together with the plane parabolic generates the
whole point join, by maximality and its nontrivial action on u. -/
theorem LocalFiveData.component_sup_plane_centralizer {c : Context D t v I}
    (m : LocalFiveData c) : L ⊔ planeCentralizer T t v I = pointJoin T v I := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  have hLH : L ≤ H := c.escaping.strict.le.trans le_sup_left
  have hCH : C ≤ H := inf_le_left
  have hstrict : C.subgroupOf H < (L ⊔ C).subgroupOf H := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨comap_mono le_sup_right,?_⟩
    intro h
    apply m.component_not_le_plane_centralizer
    intro x hx
    exact h (show (⟨x,hLH hx⟩ : H) ∈ (L ⊔ C).subgroupOf H from
      (le_sup_left : L ≤ L ⊔ C) hx)
  have ht : (L ⊔ C).subgroupOf H = ⊤ := m.plane_maximal.2 _ hstrict
  have hh := congrArg (Subgroup.map H.subtype) ht
  rw [map_subgroupOf_eq_of_le (sup_le hLH hCH),←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

/-- The plane parabolic itself escapes M. This supplies the source choice of
a rank-one parabolic over C_T(v) outside M. -/
theorem LocalFiveData.plane_centralizer_escapes {c : Context D t v I}
    (m : LocalFiveData c) : ¬ planeCentralizer T t v I ≤ D.maximalLocal := by
  intro hC
  have hLM : L ≤ D.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hH : pointJoin T v I ≤ D.maximalLocal := by
    rw [←m.component_sup_plane_centralizer]
    exact sup_le hLM hC
  exact c.escaping.escapes ((le_sup_left : I ≤ pointJoin T v I).trans hH)

/-- A rank-one overgroup of the original point Sylow lies in the plane
centralizer and escapes M. All subgroups are embedded in the original G. -/
theorem LocalFiveData.exists_escaping_rankOne {c : Context D t v I}
    (m : LocalFiveData c) :
    ∃ P : Subgroup G, pointSylow T v ⋖ P ∧ P ≤ planeCentralizer T t v I ∧
      ¬ P ≤ D.maximalLocal ∧ Chapter1.IsSylowIn 2 (pointSylow T v) P := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  obtain ⟨S,hS⟩ := c.join_sylow
  have hSC : (S : Subgroup H) ≤ C.subgroupOf H := by
    intro s hs
    exact ⟨s.property,m.pointSylow_centralizes_plane (hS ▸ mem_map_of_mem H.subtype hs)⟩
  have hSM : (S : Subgroup H) ≤ D.maximalLocal.subgroupOf H := by
    intro s hs
    exact le_normalizer_componentOrbit L T
      ((hS ▸ mem_map_of_mem H.subtype hs).1)
  have hCM : ¬ C.subgroupOf H ≤ D.maximalLocal.subgroupOf H := by
    intro h
    apply m.plane_centralizer_escapes
    intro x hx
    exact h (show (⟨x,hx.1⟩ : H) ∈ C.subgroupOf H from hx)
  obtain ⟨P,hcov,hPC,hPM⟩ := BinaryLinear.FiveFlagGeometry.exists_rankOne_escaping_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S
      (C.subgroupOf H) (D.maximalLocal.subgroupOf H) hSC hSM hCM
  have hP : P.map H.subtype ≤ C := by
    rintro _ ⟨x,hx,rfl⟩
    exact hPC hx
  have hSP : pointSylow T v ≤ P.map H.subtype := by
    rw [←hS]
    exact map_mono hcov.le
  refine ⟨P.map H.subtype,?_,hP,?_,c.join_sylow.restrict hSP
    (hP.trans inf_le_left)⟩
  · apply covBy_iff_lt_and_eq_or_eq.mpr
    constructor
    · refine lt_of_le_of_ne hSP ?_
      intro he
      apply hcov.ne
      apply map_injective H.subtype_injective
      exact hS.trans he
    · intro X hSX hXP
      have hXH : X ≤ H := hXP.trans (map_subtype_le P)
      have hSX' : (S : Subgroup H) ≤ X.subgroupOf H := by
        intro x hx
        exact hSX (hS ▸ mem_map_of_mem H.subtype hx)
      have hXP' : X.subgroupOf H ≤ P := by
        have hh := comap_mono (f := H.subtype) hXP
        rwa [comap_map_eq,(MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective,sup_bot_eq] at hh
      rcases (covBy_iff_lt_and_eq_or_eq.mp hcov).2 (X.subgroupOf H) hSX' hXP' with h | h
      · apply Or.inl
        have hh := congrArg (Subgroup.map H.subtype) h
        rwa [map_subgroupOf_eq_of_le hXH,hS] at hh
      · apply Or.inr
        have hh := congrArg (Subgroup.map H.subtype) h
        rwa [map_subgroupOf_eq_of_le hXH] at hh
  · intro h
    apply hPM
    intro x hx
    exact h (mem_map_of_mem H.subtype hx)

/-- This source rank-one subgroup satisfies the genuine minimal-parabolic
condition, including nonnormality of its prescribed Sylow subgroup. -/
theorem LocalFiveData.exists_escaping_minimalParabolic {c : Context D t v I}
    (m : LocalFiveData c) :
    ∃ (S : Sylow 2 (pointJoin T v I)) (P : Subgroup (pointJoin T v I)),
      (S : Subgroup _).map (pointJoin T v I).subtype = pointSylow T v ∧
      ChapterB.IsMinimalParabolicOver S P ∧
      P.map (pointJoin T v I).subtype ≤ planeCentralizer T t v I ∧
      ¬ P.map (pointJoin T v I).subtype ≤ D.maximalLocal := by
  let H := pointJoin T v I
  obtain ⟨S,hS⟩ := c.join_sylow
  obtain ⟨P,hcov,hPC,hPM,_⟩ := m.exists_escaping_rankOne
  have hPH : P ≤ H := hPC.trans inf_le_left
  have hS' : (S : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  have hSP : (S : Subgroup H) ≤ P.subgroupOf H := by
    rw [hS']
    exact comap_mono hcov.le
  have hcov' : (S : Subgroup H) ⋖ P.subgroupOf H := by
    apply covBy_iff_lt_and_eq_or_eq.mpr
    constructor
    · refine lt_of_le_of_ne hSP ?_
      intro he
      have hh := congrArg (Subgroup.map H.subtype) he
      rw [hS,map_subgroupOf_eq_of_le hPH] at hh
      exact hcov.ne hh
    · intro X hSX hXP
      have hSm : pointSylow T v ≤ X.map H.subtype := by rw [←hS]; exact map_mono hSX
      have hPm : X.map H.subtype ≤ P := by
        have hh := map_mono (f := H.subtype) hXP
        rwa [map_subgroupOf_eq_of_le hPH] at hh
      rcases (covBy_iff_lt_and_eq_or_eq.mp hcov).2 (X.map H.subtype) hSm hPm with h | h
      · exact Or.inl (map_injective H.subtype_injective (h.trans hS.symm))
      · apply Or.inr
        apply map_injective H.subtype_injective
        rwa [map_subgroupOf_eq_of_le hPH]
  refine ⟨S,P.subgroupOf H,hS,?_,?_,?_⟩
  · apply (ChapterB.isMinimalParabolicOver_iff S _).mpr
    constructor
    · refine ⟨hcov'.lt,⟨(S : Subgroup H),⟨le_rfl,hcov'⟩,?_⟩⟩
      intro X hX
      exact ((covBy_iff_lt_and_eq_or_eq.mp hcov').2 X hX.1 hX.2.le).resolve_right hX.2.ne
    · intro hn
      have hnorm := (normal_subgroupOf_iff_le_normalizer hSP).mp hn
      rw [BinaryLinear.FiveFlagGeometry.normalizer_sylow_eq_of_two_kernel
        m.joinAction m.joinAction_surjective m.joinAction_kernel_two S] at hnorm
      exact hcov'.lt.not_ge hnorm
  · rwa [map_subgroupOf_eq_of_le hPH]
  · rwa [map_subgroupOf_eq_of_le hPH]



/-- Exactly three actual rank-one subgroups of G lie between the original
point Sylow and the plane centralizer. -/
theorem LocalFiveData.rankOne_card {c : Context D t v I} (m : LocalFiveData c) :
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

private theorem LocalFiveData.exchange_rankOne_map {c : Context D t v I}
    (m : LocalFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
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

private theorem LocalFiveData.exchange_rankOne_square {c : Context D t v I}
    (m : LocalFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
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
def LocalFiveData.rankOneExchange {c : Context D t v I} (m : LocalFiveData c) :
    RankOneBelow (pointSylow T v) (planeCentralizer T t v I) ≃
      RankOneBelow (pointSylow T v) (planeCentralizer T t v I) :=
  { toFun P := ⟨P.val.map (MulAut.conj t).toMonoidHom,
      by exact m.exchange_rankOne_map P⟩
    invFun P := ⟨P.val.map (MulAut.conj t).toMonoidHom,
      by exact m.exchange_rankOne_map P⟩
    left_inv P := by exact Subtype.ext (m.exchange_rankOne_square P)
    right_inv P := by exact Subtype.ext (m.exchange_rankOne_square P) }

@[simp] theorem LocalFiveData.rankOneExchange_apply_val {c : Context D t v I}
    (m : LocalFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
    (m.rankOneExchange P).val = P.val.map (MulAut.conj t).toMonoidHom := rfl

/-- The exchange also preserves which of these original subgroups lie in M. -/
theorem LocalFiveData.rankOneExchange_le_maximalLocal_iff {c : Context D t v I}
    (m : LocalFiveData c) (P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I)) :
    (m.rankOneExchange P).val ≤ D.maximalLocal ↔ P.val ≤ D.maximalLocal := by
  have hM : D.maximalLocal.map (MulAut.conj t).toMonoidHom = D.maximalLocal :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer
      (le_normalizer_componentOrbit L T c.escaping.t_mem))
  change P.val.map (MulAut.conj t).toMonoidHom ≤ D.maximalLocal ↔ _
  conv_lhs => rw [←hM]
  exact map_le_map_iff_of_injective (MulAut.conj t).injective

/-- Once two distinct internal source nodes are identified in M, the third
node is the unique rank-one parabolic escaping M. -/
theorem LocalFiveData.exists_unique_escaping_rankOne_of_pair {c : Context D t v I}
    (m : LocalFiveData c)
    (A B : RankOneBelow (pointSylow T v) (planeCentralizer T t v I))
    (hAB : A ≠ B) (hAM : A.val ≤ D.maximalLocal) (hBM : B.val ≤ D.maximalLocal) :
    ∃! P : RankOneBelow (pointSylow T v) (planeCentralizer T t v I),
      ¬ P.val ≤ D.maximalLocal := by
  apply existsUnique_rankOne_escaping_of_pair _ _ D.maximalLocal m.rankOne_card A B hAB hAM hBM
  obtain ⟨P,hP,hPC,hPM,_⟩ := m.exists_escaping_rankOne
  exact ⟨⟨P,hP,hPC⟩,hPM⟩

/-- The escaping source parabolic is normalized by the original t; this
uses the three-node lattice, preservation of M, and the two internal nodes. -/
theorem LocalFiveData.exchange_fixes_escaping_rankOne_of_pair {c : Context D t v I}
    (m : LocalFiveData c)
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
theorem LocalFiveData.exists_exchange_fixed_escaping_rankOne_of_moved_node
    {c : Context D t v I} (m : LocalFiveData c)
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
theorem LocalFiveData.rankOne_isMinimalParabolic {c : Context D t v I}
    (m : LocalFiveData c)
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
theorem LocalFiveData.exists_exchange_fixed_minimalParabolic_of_moved_node
    {c : Context D t v I} (m : LocalFiveData c)
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



private theorem PointNode_natural_coordinates_injective {c : Context D t v I} (m : LocalFiveData c) :
    Function.Injective m.natural.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [m.natural.kernel_eq,bot_subgroupOf]

private theorem natural_point_ne {c : Context D t v I} (m : LocalFiveData c) :
    (m.natural.coordinates ⟨oppositePoint t v,m.opposite_mem_moved⟩).toAdd ≠ 0 := by
  intro hz
  have hh := (m.natural.coordinates_eq_one_iff
    ⟨oppositePoint t v,m.opposite_mem_moved⟩).mp hz
  exact c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp hh)

/-- The original centralizer is the literal preimage of a model vector stabilizer. -/
theorem LocalFiveData.componentPointCentralizer_eq_comap {c : Context D t v I} (m : LocalFiveData c) :
    (componentPointCentralizer L t v).subgroupOf L =
      (MulAction.stabilizer SL(3,ZMod 2)
        (m.natural.coordinates ⟨oppositePoint t v,m.opposite_mem_moved⟩).toAdd).comap
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) := by
  ext l
  let u : (⁅D.moduleSubgroup,L⁆ : Subgroup G) :=
    ⟨oppositePoint t v,m.opposite_mem_moved⟩
  have hh := m.natural.equivariant l u
  change (l : G) ∈ L ⊓ centralizer ({oppositePoint t v} : Set G) ↔ _
  simp only [mem_inf, l.property, true_and, mem_centralizer_singleton_iff]
  change _ ↔ m.quotient (QuotientGroup.mk' (pCore 2 L) l) •
    (m.natural.coordinates u).toAdd = (m.natural.coordinates u).toAdd
  constructor
  · intro he
    have hc : (⟨(l : G)*u*(l : G)⁻¹,
        (mem_normalizer_iff.mp (m.natural.normalized l.property) u).mp u.property⟩ :
        (⁅D.moduleSubgroup,L⁆ : Subgroup G)) = u := by
      apply Subtype.ext
      change (l : G)*oppositePoint t v*(l : G)⁻¹ = oppositePoint t v
      rw [he,mul_inv_cancel_right]
    rw [hc] at hh
    exact hh.symm
  · intro he
    change _ = m.quotient (QuotientGroup.mk' (pCore 2 L) l) •
      (m.natural.coordinates u).toAdd at hh
    rw [he] at hh
    have hc := congrArg Subtype.val (PointNode_natural_coordinates_injective m
      (Multiplicative.toAdd.injective hh))
    change (l : G)*oppositePoint t v*(l : G)⁻¹ = oppositePoint t v at hc
    exact (mul_inv_eq_iff_eq_mul).mp hc

theorem LocalFiveData.componentPointCentralizer_index {c : Context D t v I}
    (m : LocalFiveData c) :
    ((componentPointCentralizer L t v).subgroupOf L).index = 7 := by
  rw [m.componentPointCentralizer_eq_comap,index_comap_of_surjective _
    (m.quotient.surjective.comp (QuotientGroup.mk'_surjective _))]
  exact BinaryLinear.NaturalThreePoint.stabilizer_index _ (natural_point_ne m)


/-- The literal component point centralizer has the source order. -/
theorem LocalFiveData.componentPointCentralizer_card {c : Context D t v I}
    (m : LocalFiveData c) :
    Nat.card (componentPointCentralizer L t v) = 24 * Nat.card (pCore 2 L) := by
  have hc := ((componentPointCentralizer L t v).subgroupOf L).index_mul_card
  rw [m.componentPointCentralizer_index,
    Nat.card_congr (subgroupOfEquivOfLe (show componentPointCentralizer L t v ≤ L from
      inf_le_left)).toEquiv] at hc
  have hL : Nat.card L = 168 * Nat.card (pCore 2 L) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),
      Nat.card_congr m.quotient.toEquiv,BinaryLinear.NaturalThreePoint.group_card]
  rw [hL] at hc
  omega

/-- The original point Sylow normalizes C_L(u). -/
theorem LocalFiveData.pointSylow_normalizes_componentPointCentralizer
    {c : Context D t v I} (m : LocalFiveData c) :
    pointSylow T v ≤ normalizer (componentPointCentralizer L t v : Set G) := by
  have hSC : pointSylow T v ≤ centralizer ({oppositePoint t v} : Set G) :=
    m.pointSylow_centralizes_plane.trans (centralizer_le (Set.singleton_subset_iff.mpr
      ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))))
  exact (le_inf c.escaping.sylow_normalizes
    (hSC.trans (centralizer ({oppositePoint t v} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- The source node lies in the actual plane centralizer. -/
theorem LocalFiveData.componentPointNode_le_plane {c : Context D t v I}
    (m : LocalFiveData c) : componentPointNode T L t v ≤ planeCentralizer T t v I := by
  change componentPointNode T L t v ≤ pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)
  rw [c.join_plane_centralizer]
  apply sup_le
  · exact le_inf ((show componentPointCentralizer L t v ≤ L from inf_le_left).trans
      (c.escaping.strict.le.trans le_sup_left)) inf_le_right
  · exact le_inf le_sup_right (m.pointSylow_centralizes_plane.trans
      (centralizer_le (Set.singleton_subset_iff.mpr
        ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _)))))

/-- The source node is contained in the original maximal local subgroup. -/
theorem LocalFiveData.componentPointNode_le_maximalLocal {c : Context D t v I}
    (_m : LocalFiveData c) : componentPointNode T L t v ≤ D.maximalLocal := by
  exact sup_le ((show componentPointCentralizer L t v ≤ L from inf_le_left).trans
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer))
    ((show pointSylow T v ≤ T from inf_le_left).trans (le_normalizer_componentOrbit L T))

private theorem normalized_sup_index (Y S : Subgroup G)
    (hn : S ≤ normalizer (Y : Set G)) : S.relIndex (Y ⊔ S) = S.relIndex Y := by
  let J := Y ⊔ S
  let _ : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hn)
  have aux (A B : Subgroup J) [A.Normal] : B.relIndex (A ⊔ B) = B.relIndex A := by
    have hm : A.relIndex B * B.relIndex (A ⊔ B) = A.relIndex B * B.relIndex A := by
      calc
        _ = (B ⊓ A).relIndex (A ⊔ B) := by
          rw [← inf_relIndex_left (H := B) (K := A)]
          exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
        _ = (B ⊓ A).relIndex A * A.relIndex (A ⊔ B) :=
          (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
        _ = _ := by simp [inf_relIndex_right, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (index_ne_zero_of_finite : A.relIndex B ≠ 0)) hm
  have hi := aux (Y.subgroupOf J) (S.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at hi
  exact hi

/-- Adjoining the literal component centralizer to C_T(v) gives index three. -/
theorem LocalFiveData.componentPointNode_index {c : Context D t v I}
    (m : LocalFiveData c) : (pointSylow T v).relIndex (componentPointNode T L t v) = 3 := by
  let S := pointSylow T v
  let A := componentPointCentralizer L t v
  let P := componentPointNode T L t v
  have hi : S.relIndex P = S.relIndex A :=
    normalized_sup_index A S m.pointSylow_normalizes_componentPointCentralizer
  have hd : S.relIndex P ∣ Nat.card A := hi ▸ relIndex_dvd_card _ _
  have hs : Chapter1.IsSylowIn 2 S P :=
    c.join_sylow.restrict le_sup_right (m.componentPointNode_le_plane.trans inf_le_left)
  obtain ⟨U,hU⟩ := hs
  have hind : S.relIndex P = (U : Subgroup P).index := by
    have hh := congrArg (Subgroup.comap P.subtype) hU
    rw [comap_map_eq,(MonoidHom.ker_eq_bot_iff P.subtype).mpr P.subtype_injective,
      sup_bot_eq] at hh
    exact congrArg Subgroup.index hh.symm
  have hodd : ¬ 2 ∣ S.relIndex P := hind ▸ U.not_dvd_index
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  have hcard : Nat.card A = 2^(n+3) * 3 := by
    change Nat.card (componentPointCentralizer L t v) = _
    rw [m.componentPointCentralizer_card,hn,pow_add]
    ring
  rw [hcard] at hd
  have hcop : (S.relIndex P).Coprime 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd).symm
  have hd3 := (hcop.pow_right (n+3)).dvd_of_dvd_mul_left hd
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with he | he
  · have hAS : A ≤ S := le_sup_left.trans (relIndex_eq_one.mp he)
    have hp := ((Chapter1.isSylowIn_iff.mp c.join_sylow).1).to_le hAS
    have hdA : 3 ∣ Nat.card A := hcard ▸ dvd_mul_left 3 _
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk] at hdA
    exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdA) |>.elim
  · exact he

/-- This is one of the three actual rank-one nodes of the plane parabolic. -/
theorem LocalFiveData.componentPointNode_covBy {c : Context D t v I}
    (m : LocalFiveData c) : pointSylow T v ⋖ componentPointNode T L t v := by
  have hS : pointSylow T v ≤ componentPointNode T L t v := le_sup_right
  have hi := m.componentPointNode_index
  apply covBy_iff_lt_and_eq_or_eq.mpr
  constructor
  · exact lt_of_le_of_ne hS (fun he => by simp [←he] at hi)
  · intro Q hSQ hQP
    have hm := relIndex_mul_relIndex (pointSylow T v) Q (componentPointNode T L t v) hSQ hQP
    rw [hi] at hm
    have hp : ((pointSylow T v).relIndex Q * Q.relIndex (componentPointNode T L t v)).Prime :=
      hm ▸ Nat.prime_three
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hQ⟩ | ⟨_,hS'⟩
    · exact Or.inr (le_antisymm hQP (relIndex_eq_one.mp hQ))
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp hS') hSQ)



private theorem NodeExchange_natural_coordinates_injective {c : Context D t v I} (m : LocalFiveData c) :
    Function.Injective m.natural.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [m.natural.kernel_eq,bot_subgroupOf]

private def normalizerQuotient {c : Context D t v I} (m : LocalFiveData c) :
    normalizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G) →* SL(3,ZMod 2) :=
  (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
    (BinaryConjugationSection.normalizerAction m.natural.coordinates
      ⟨NodeExchange_natural_coordinates_injective m,m.natural.onto⟩)

private theorem normalizerQuotient_restrict {c : Context D t v I} (m : LocalFiveData c)
    (l : L) : normalizerQuotient m ⟨(l : G),m.natural.normalized l.property⟩ =
      m.quotient (QuotientGroup.mk' (pCore 2 L) l) := by
  apply (BinaryLinear.OuterCyclic.slEquivLinear 3).injective
  change (BinaryLinear.OuterCyclic.slEquivLinear 3)
    ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  apply LinearEquiv.toLinearMap_injective
  exact BinaryConjugationSection.normalizerAction_restrict m.natural
    (NodeExchange_natural_coordinates_injective m) l

private theorem normalizerQuotient_centralizer {c : Context D t v I} (m : LocalFiveData c)
    (g : normalizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G))
    (hc : (g : G) ∈ centralizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G)) :
    normalizerQuotient m g = 1 := by
  apply (BinaryLinear.OuterCyclic.slEquivLinear 3).injective
  change (BinaryLinear.OuterCyclic.slEquivLinear 3)
    ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm _) = _
  rw [MulEquiv.apply_symm_apply,map_one]
  apply LinearEquiv.ext
  intro w
  change BinaryConjugationSection.normalizerAction m.natural.coordinates
    ⟨NodeExchange_natural_coordinates_injective m,m.natural.onto⟩ g w = w
  obtain ⟨a,ha⟩ := m.natural.onto (Multiplicative.ofAdd w)
  have hw : (m.natural.coordinates a).toAdd = w := congrArg Multiplicative.toAdd ha
  rw [←hw]
  have he : (⁅D.moduleSubgroup,L⁆ : Subgroup G).normalizerMonoidHom g a = a := by
    apply Subtype.ext
    change (g : G)*(a : G)*(g : G)⁻¹ = a
    rw [←hc a a.property,mul_inv_cancel_right]
  exact (BinaryConjugationSection.normalizerAction_coordinates m.natural.coordinates
    ⟨NodeExchange_natural_coordinates_injective m,m.natural.onto⟩ g a).trans
      (congrArg (fun x => (m.natural.coordinates x).toAdd) he)

/-- The crossed component centralizes the original natural factor. -/
theorem LocalFiveData.conjugate_component_centralizes_moved {c : Context D t v I}
    (_m : LocalFiveData c) :
    L.map (MulAut.conj t).toMonoidHom ≤ centralizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G) :=
  (le_centralizer_iff.mp c.moved_centralizes_opposite).trans
    (centralizer_le (commutator_mono (le_componentOrbit _ _) le_rfl))

/-- The original component point node is moved by the exchange. -/
theorem LocalFiveData.componentPointNode_moved {c : Context D t v I}
    (m : LocalFiveData c) :
    (componentPointNode T L t v).map (MulAut.conj t).toMonoidHom ≠
      componentPointNode T L t v := by
  let W : Subgroup G := ⁅D.moduleSubgroup,L⁆
  let N := normalizer (W : Set G)
  let C := centralizer (W : Set G)
  let S := pointSylow T v
  let A := componentPointCentralizer L t v
  let P := componentPointNode T L t v
  let q := normalizerQuotient m
  let f := m.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hSN : S ≤ N := by
    intro s hs
    exact c.halfJoin_normalizes_local_moved
      ((show (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ halfJoin T L from le_sup_right)
        ⟨hs.1,c.escaping.sylow_normalizes hs⟩)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hmap : P.map (MulAut.conj t).toMonoidHom ≤ C ⊔ S := by
    change (A ⊔ S).map _ ≤ _
    have hS : S.map (MulAut.conj t).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (m.pointSylow_normalized c.escaping.t_mem)
    rw [Subgroup.map_sup,hS]
    exact sup_le_sup ((map_mono (show A ≤ L from inf_le_left)).trans
      m.conjugate_component_centralizes_moved) le_rfl
  have hCq : (C.subgroupOf N).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro g hg
    exact normalizerQuotient_centralizer m g hg
  have hSq : IsPGroup 2 ((S.subgroupOf N).map q) :=
    ((Chapter1.isSylowIn_iff.mp c.join_sylow).1.comap_subtype).map q
  intro he
  have hPC : P ≤ C ⊔ S := by
    change P.map (MulAut.conj t).toMonoidHom = P at he
    rwa [he] at hmap
  have hPq : IsPGroup 2 ((P.subgroupOf N).map q) := by
    apply hSq.to_le
    calc
      _ ≤ ((C ⊔ S).subgroupOf N).map q := map_mono (comap_mono hPC)
      _ = (C.subgroupOf N).map q ⊔ (S.subgroupOf N).map q := by
        rw [subgroupOf_sup hCN hSN,Subgroup.map_sup]
      _ = (S.subgroupOf N).map q := by rw [hCq,bot_sup_eq]
  have hAq : (A.subgroupOf L).map f ≤ (P.subgroupOf N).map q := by
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨⟨(a : G),m.natural.normalized a.property⟩,
      (show A ≤ P from le_sup_left) ha,?_⟩
    exact normalizerQuotient_restrict m a
  have hAf : IsPGroup 2 ((A.subgroupOf L).map f) := hPq.to_le hAq
  let u := (m.natural.coordinates ⟨oppositePoint t v,m.opposite_mem_moved⟩).toAdd
  have hu : u ≠ 0 := by
    intro hz
    have hh := (m.natural.coordinates_eq_one_iff
      ⟨oppositePoint t v,m.opposite_mem_moved⟩).mp hz
    exact c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp hh)
  have hEq : (A.subgroupOf L).map f = MulAction.stabilizer SL(3,ZMod 2) u := by
    rw [m.componentPointCentralizer_eq_comap,map_comap_eq_self_of_surjective hf]
  rw [hEq] at hAf
  obtain ⟨n,hn⟩ := hAf.exists_card_eq
  rw [BinaryLinear.NaturalThreePoint.stabilizer_card u hu] at hn
  have hd : 3 ∣ 2^n := hn ▸ (by decide : 3 ∣ 24)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- Source choice of an escaping, exchange-fixed minimal parabolic, with
Pc and its distinct conjugate now constructed in the original group. -/
theorem LocalFiveData.exists_exchange_fixed_minimalParabolic {c : Context D t v I}
    (m : LocalFiveData c) :
    ∃ (S : Sylow 2 (pointJoin T v I)) (P : Subgroup (pointJoin T v I)),
      (S : Subgroup _).map (pointJoin T v I).subtype = pointSylow T v ∧
      ChapterB.IsMinimalParabolicOver S P ∧
      P.map (pointJoin T v I).subtype ≤ planeCentralizer T t v I ∧
      ¬ P.map (pointJoin T v I).subtype ≤ D.maximalLocal ∧
      t ∈ normalizer (P.map (pointJoin T v I).subtype : Set G) := by
  let Pc : BinaryLinear.FiveFlagGeometry.RankOneBelow (pointSylow T v)
      (planeCentralizer T t v I) :=
    ⟨componentPointNode T L t v,m.componentPointNode_covBy,m.componentPointNode_le_plane⟩
  apply m.exists_exchange_fixed_minimalParabolic_of_moved_node Pc
    m.componentPointNode_le_maximalLocal
  intro he
  exact m.componentPointNode_moved (congrArg Subtype.val he)


end CFSG.Quasithin.Chapter10.PointControl.Constrained
