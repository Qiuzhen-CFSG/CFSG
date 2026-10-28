module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Remaining
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups
public import Theory.GroupTheory.SolvableMutualCommutator

/-!
# Solvable normal closures in the remaining Janko projection

The point residual and either the three-space or six-space residual generate L.
An explicit exterior transvection shows L does not preserve the corresponding
proper subspace. Thus the intersection of L₁ with Gᵢ is proper. It contains
O₂(L₁), since that core lies in the original Sylow T. Proper subgroups of the
actual SL₃(2) quotient are solvable, so this intersection is solvable.

The source factorization M₁ = PL₁ then expresses M₁ ∩ Mᵢ as the product of
P with that intersection. Both factors are solvable and P normalizes the
intersection. Consequently the literal projected normal closure of Y* is
solvable. It remains a non-two-group, and in the J₄ row its projected actor
is proper: a full actor would give a nontrivial solvable normal subgroup of
the actual simple point-component image. Simplicity is inherited from the
source C-component and the certified trivial model center.

The final application refines every remaining failure of G₃,G₆ ≤ N_G(L)
with these constraints, retaining the original Sylow and full point-core
quotient. It does not assert the J₄ parabolic placement or overgroup exclusion.
That model argument and local source assembly remain with qt-d-1251-local;
Structural1222At and final exterior discharge retain qt-d-1222-source and
qt-d-1251-source respectively. No generation-one exclusion is used.
Source: Aschbacher--Smith, 12.5.3--4, printed pp.818--819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

omit [Finite G] in
private theorem component_not_le_local (i : ℕ) (hi : i = 3 ∨ i = 6) :
    ¬ L ≤ s.marking.Gi i := by
  intro he
  let g := Representation.SL5TenDimensional.elementary (4 : Fin 5) 0
  obtain ⟨l,hl⟩ := s.marking.componentActor_surjective g
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hg := (s.marking.mem_Gi_iff_actor i hidx l).mp (he l.property)
  rw [hl,Representation.SL5ExteriorSquare.mem_parabolic_iff_lowerLeft_zero] at hg
  have hb := hg 4 0 (by rcases hi with rfl | rfl <;> decide) (by
    rcases hi with rfl | rfl <;> decide)
  have hg40 : g.val 4 0 = 1 := by decide +kernel
  rw [hg40] at hb
  exact one_ne_zero hb

/-- The original point residual does not preserve either other local subspace. -/
theorem point_residual_not_le_local_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) : ¬ s.marking.Li 1 ≤ s.marking.Gi i := by
  intro he
  apply s.component_not_le_local i hi
  exact (s.point_residual_sup_local_eq h i hi).symm.le.trans
    (sup_le he (s.marking.Li_le_Gi i))

/-- The proper intersection with the point residual retains its full two-core. -/
theorem point_residual_local_intersection_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    Group.IsSolvable (s.marking.Li 1 ⊓ s.marking.Gi i : Subgroup G) := by
  let B := s.marking.Li 1
  let N := B ⊓ s.marking.Gi i
  let A := N.subgroupOf B
  have hne : A ≠ ⊤ := by
    intro he
    apply s.point_residual_not_le_local_normalizer h i hi
    intro x hx
    have hh : (⟨x,hx⟩ : B) ∈ A := he ▸ mem_top _
    exact hh.2
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T B
    (s.sylow_normalizes_Li 1 (.inl rfl))
  have hc : pCore 2 B ≤ A := by
    intro x hx
    have hs := pCore_isPGroup.le_sylow_of_normal S hx
    rw [hS] at hs
    have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
    exact ⟨x.property,s.sylow_le_Gi i hidx hs⟩
  let : Group.IsSolvable A := Matrix.PSL3Two.isSolvable_proper_subgroup_containing_twoCore
    (s.marking.LiCoreEquiv 1 (.inl rfl)) A hne hc
  exact Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe (show N ≤ B from inf_le_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show N ≤ B from inf_le_left)).surjective

/-- The two original normalizers inside LT have a solvable intersection. -/
theorem point_parabolic_local_intersection_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    Group.IsSolvable (s.marking.Mi 1 ⊓ s.marking.Mi i : Subgroup G) := by
  let N := s.marking.Li 1 ⊓ s.marking.Gi i
  have he : s.marking.Mi 1 ⊓ s.marking.Mi i = s.P ⊔ N := by
    apply le_antisymm
    · intro x hx
      have hp : x ∈ (s.P : Set G) * (s.marking.Li 1 : Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right _ _
          (s.P_le_M₁.trans (s.Mi_normalizes_Li 1)),←s.M₁_eq_P_sup_point_residual]
        exact hx.1
      obtain ⟨p,hp,b,hb,rfl⟩ := hp
      have hbi : b ∈ s.marking.Gi i := by
        have hh := (s.marking.Gi i).mul_mem
          ((s.marking.Gi i).inv_mem ((s.P_le_Mi i hi hp).2)) hx.2.2
        simpa only [inv_mul_cancel_left] using hh
      exact mul_mem_sup hp ⟨hb,hbi⟩
    · exact sup_le (le_inf s.P_le_M₁ (s.P_le_Mi i hi))
        (le_inf (inf_le_left.trans (s.Li_le_Mi 1))
          (le_inf ((inf_le_left.trans (s.marking.Li_le_L 1)).trans le_sup_left) inf_le_right))
  have hn : s.P ≤ normalizer (N : Set G) :=
    (le_inf (s.P_le_M₁.trans (s.Mi_normalizes_Li 1))
      ((s.P_le_Mi i hi).trans (inf_le_right.trans (s.marking.Gi i).le_normalizer))).trans
      inf_normalizer_le_normalizer_inf
  let : Group.IsSolvable N := s.point_residual_local_intersection_solvable h i hi
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable s.P := (T : Subgroup G).isSolvable_of_relIndex_le_four s.P
    (by rw [s.sylow_relIndex_P]; decide)
  rw [he,sup_comm]
  exact Group.isSolvable_sup_of_normalizes N s.P hn

/-- The literal projected Y-closure is solvable, without a model-placement premise. -/
theorem projected_Y_span_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) (hY : s.Y ≤ K)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    Group.IsSolvable (conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i)) := by
  let B := s.marking.Mi 1 ⊓ s.marking.Mi i
  let : Group.IsSolvable B := s.point_parabolic_local_intersection_solvable h i hi
  let b := subgroupOfEquivOfLe (show B ≤ s.marking.Gi 1 from inf_le_left.trans inf_le_right)
  let : Group.IsSolvable (B.subgroupOf (s.marking.Gi 1)) :=
    Group.isSolvable_of_isSolvable_injective (f := b.toMonoidHom) b.injective
  let : Group.IsSolvable (s.pointCoreImage B) := Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))).subgroupMap_surjective _)
  have hb : s.marking.Li i ⊓ s.marking.Gi 1 ≤ B := by
    exact le_inf
      (le_inf ((inf_le_left.trans (s.marking.Li_le_L i)).trans le_sup_left) inf_le_right)
      (inf_le_left.trans (s.Li_le_Mi i))
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (((s.projected_Y_span_le_original_intersection h hN hY i hi).trans
      inf_le_left).trans (s.pointCoreImage_mono hb))) (inclusion_injective _)

/-- The same literal normal closure has an odd-order section. -/
theorem projected_Y_span_not_two {K : Subgroup G} (i : ℕ) :
    ¬ IsPGroup 2 (conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i)) := by
  intro hp
  exact s.pointCoreImage_Y_not_two (hp.to_le (le_conjugateSpanBy _ _))

/-- Simplicity of the actual Janko point image follows from its source component
and trivial model center; no independent simplicity certificate is assumed. -/
theorem pointCoreImage_simple_of_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    IsSimpleGroup (s.pointCoreImage K) := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := s.point_component_quasisimple_of_not_fortyNine h hK hLK
    (by rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card]; decide)
  let e := s.pointComponentCoreEquivImage hK.1 hN
  let : IsQuasisimple (s.pointCoreImage K) := IsQuasisimple.of_mulEquiv e
  let a := e.symm.trans hm.some
  have hz : center (s.pointCoreImage K) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply a.injective
    rw [map_one]
    have hh : a x ∈ center Janko4.Model := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := a.surjective y
      simpa only [map_mul] using congrArg a (mem_center_iff.mp hx y)
    exact mem_bot.mp (Janko4.model_center_eq_bot ▸ hh)
  let := IsQuasisimple.simple (G := s.pointCoreImage K)
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

/-- The projected actor is a proper subgroup of the Janko component.
Otherwise its solvable normal Y-closure would be a nontrivial normal subgroup
of the inherited simple component. -/
theorem localPointProjection_ne_pointComponent_of_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.localPointProjection K i ≠ s.pointCoreImage K := by
  intro he
  have hYK := s.Y_le_point_component_of_large_model h hK hN (.inr (.inr hm))
  let C := s.pointCoreImage K
  let N := conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i)
  have hNC : N ≤ C := (s.projected_Y_span_le_original_intersection h hN hYK i hi).trans inf_le_right
  have hnC : C ≤ normalizer (N : Set _) :=
    he.symm.le.trans (le_normalizer_conjugateSpanBy _ _)
  let : (N.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hNC).mpr hnC
  let : IsSimpleGroup C := s.pointCoreImage_simple_of_janko h hK hLK hN hm
  rcases (inferInstance : (N.subgroupOf C).Normal).eq_bot_or_eq_top with hn | hn
  · have hn0 : N = ⊥ := by
      have hh := congrArg (map C.subtype) hn
      rwa [map_subgroupOf_eq_of_le hNC,Subgroup.map_bot] at hh
    have htwo : IsPGroup 2 N := hn0 ▸ (show IsPGroup 2 (⊥ : Subgroup _) from IsPGroup.of_bot)
    exact s.projected_Y_span_not_two i htwo
  · have hCN : C ≤ N := by
      intro x hx
      exact (show (⟨x,hx⟩ : C) ∈ N.subgroupOf C from hn ▸ mem_top _)
    let : Group.IsSolvable N := s.projected_Y_span_solvable h hN hYK i hi
    let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hCN) (inclusion_injective hCN)
    let : Group.IsPerfect (K.subgroupOf (s.marking.Gi 1)) := hK.2.perfect
    let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
      (f := (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))).subgroupMap
        (K.subgroupOf (s.marking.Gi 1)))
      ((QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))).subgroupMap_surjective _)
    exact Group.IsPerfect.not_isSolvable C inferInstance

/-- Every remaining source normalizer escape supplies a proper Janko Sylow
overgroup with the literal solvable, non-two normal Y-closure. These are
additional proved constraints on the model placement still required in 12.5.4. -/
theorem exists_janko_solvable_span_of_local_normalizer_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (he : ¬ s.marking.Gi i ≤ s.marking.M) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      s.marking.Li 1 ≤ K ∧ (K.subgroupOf (s.marking.Gi 1)).Normal ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) ∧ s.Y ≤ K ∧
      s.localPointProjection K i < s.pointCoreImage K ∧
      Group.IsSolvable (conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i)) ∧
      ¬ IsPGroup 2 (conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i)) ∧
      ¬ s.localPointProjection K i ≤ normalizer (s.pointCoreImage (s.marking.Li 1) : Set _) := by
  obtain ⟨K,hK,hLK,hN,hm,hYK,hfail⟩ :=
    s.exists_janko_point_projection_of_local_normalizer_escape h i hi he
  exact ⟨K,hK,hLK,hN,hm,hYK,lt_of_le_of_ne inf_le_left
    (s.localPointProjection_ne_pointComponent_of_janko h hK hLK hN hm i hi),
    s.projected_Y_span_solvable h hN hYK i hi,s.projected_Y_span_not_two i,hfail⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
