module
public import Theory.SpecificGroups.SL3.BinaryPointStabilizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Exchange

/-!
# The component point node in the literal plane parabolic

The original natural-three quotient identifies C_L(u) with the preimage
of a nonzero vector stabilizer. Its index seven and order 24 |O₂(L)|,
together with the prescribed Sylow property, show that
P_c = C_L(u) C_T(v) covers C_T(v) with index three. This node lies in the
actual plane centralizer and in the original maximal local subgroup.

Source: Aschbacher--Smith, 10.2.9, printed p.753. The source exchange and
terminal contradictions are retained by qt-d-10-nona5-point-constrained.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

abbrev componentPointCentralizer (L : Subgroup G) (t v : G) : Subgroup G :=
  L ⊓ centralizer ({oppositePoint t v} : Set G)

abbrev componentPointNode (T : Sylow 2 G) (L : Subgroup G) (t v : G) : Subgroup G :=
  componentPointCentralizer L t v ⊔ pointSylow T v

private theorem natural_coordinates_injective {c : Context D t v I} (m : LinearFiveData c) :
    Function.Injective m.natural.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [m.natural.kernel_eq,bot_subgroupOf]

private theorem natural_point_ne {c : Context D t v I} (m : LinearFiveData c) :
    (m.natural.coordinates ⟨oppositePoint t v,m.opposite_mem_moved⟩).toAdd ≠ 0 := by
  intro hz
  have hh := (m.natural.coordinates_eq_one_iff
    ⟨oppositePoint t v,m.opposite_mem_moved⟩).mp hz
  exact c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp hh)

/-- The original centralizer is the literal preimage of a model vector stabilizer. -/
theorem LinearFiveData.componentPointCentralizer_eq_comap {c : Context D t v I} (m : LinearFiveData c) :
    (componentPointCentralizer L t v).subgroupOf L =
      (MulAction.stabilizer SL(3,ZMod 2)
        (m.natural.coordinates ⟨oppositePoint t v,m.opposite_mem_moved⟩).toAdd).comap
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) := by
  ext l
  let u : (⁅D.fullModule,L⁆ : Subgroup G) :=
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
        (⁅D.fullModule,L⁆ : Subgroup G)) = u := by
      apply Subtype.ext
      change (l : G)*oppositePoint t v*(l : G)⁻¹ = oppositePoint t v
      rw [he,mul_inv_cancel_right]
    rw [hc] at hh
    exact hh.symm
  · intro he
    change _ = m.quotient (QuotientGroup.mk' (pCore 2 L) l) •
      (m.natural.coordinates u).toAdd at hh
    rw [he] at hh
    have hc := congrArg Subtype.val (natural_coordinates_injective m
      (Multiplicative.toAdd.injective hh))
    change (l : G)*oppositePoint t v*(l : G)⁻¹ = oppositePoint t v at hc
    exact (mul_inv_eq_iff_eq_mul).mp hc

theorem LinearFiveData.componentPointCentralizer_index {c : Context D t v I}
    (m : LinearFiveData c) :
    ((componentPointCentralizer L t v).subgroupOf L).index = 7 := by
  rw [m.componentPointCentralizer_eq_comap,index_comap_of_surjective _
    (m.quotient.surjective.comp (QuotientGroup.mk'_surjective _))]
  exact BinaryLinear.NaturalThreePoint.stabilizer_index _ (natural_point_ne m)


/-- The literal component point centralizer has the source order. -/
theorem LinearFiveData.componentPointCentralizer_card {c : Context D t v I}
    (m : LinearFiveData c) :
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
theorem LinearFiveData.pointSylow_normalizes_componentPointCentralizer
    {c : Context D t v I} (m : LinearFiveData c) :
    pointSylow T v ≤ normalizer (componentPointCentralizer L t v : Set G) := by
  have hSC : pointSylow T v ≤ centralizer ({oppositePoint t v} : Set G) :=
    m.pointSylow_centralizes_plane.trans (centralizer_le (Set.singleton_subset_iff.mpr
      ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))))
  exact (le_inf c.escaping.sylow_normalizes
    (hSC.trans (centralizer ({oppositePoint t v} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- The source node lies in the actual plane centralizer. -/
theorem LinearFiveData.componentPointNode_le_plane {c : Context D t v I}
    (m : LinearFiveData c) : componentPointNode T L t v ≤ planeCentralizer T t v I := by
  change componentPointNode T L t v ≤ pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)
  rw [c.join_plane_centralizer]
  apply sup_le
  · exact le_inf ((show componentPointCentralizer L t v ≤ L from inf_le_left).trans
      (c.escaping.strict.le.trans le_sup_left)) inf_le_right
  · exact le_inf le_sup_right (m.pointSylow_centralizes_plane.trans
      (centralizer_le (Set.singleton_subset_iff.mpr
        ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _)))))

/-- The source node is contained in the original maximal local subgroup. -/
theorem LinearFiveData.componentPointNode_le_maximalLocal {c : Context D t v I}
    (_m : LinearFiveData c) : componentPointNode T L t v ≤ D.maximalLocal := by
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
theorem LinearFiveData.componentPointNode_index {c : Context D t v I}
    (m : LinearFiveData c) : (pointSylow T v).relIndex (componentPointNode T L t v) = 3 := by
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
theorem LinearFiveData.componentPointNode_covBy {c : Context D t v I}
    (m : LinearFiveData c) : pointSylow T v ⋖ componentPointNode T L t v := by
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

end CFSG.Quasithin.Chapter10.PointControl.Constrained
