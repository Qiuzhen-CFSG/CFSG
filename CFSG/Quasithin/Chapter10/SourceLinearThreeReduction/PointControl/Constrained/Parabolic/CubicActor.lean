module
public import Theory.GroupTheory.CoprimeQuotientSubgroups.SeparatedPair
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ThreeFree
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerResidual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.ResidualLocal

/-!
# The actual nine-group in the two moving parabolics

The noncentralizing node meets the centralizer of u exactly in C_T(v).
Its order is divisible by three, and its cubic subgroup lies in L because
L C_T(v)/L is a two-group. Its conjugate fixes u and moves v. The original
factors commute modulo O₂(L₀), which centralizes the full source module.
A common coprime lift therefore supplies an elementary nine-group inside
the two moving nodes, disjoint from the centralizer of the original plane.

Source: Aschbacher--Smith, 10.2.9, printed p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- A proper Sylow overgroup in the actual five-space action has a cubic divisor. -/
theorem LinearFiveData.three_dvd_sylow_overgroup {c : Context D t v I}
    (m : LinearFiveData c) (F : Subgroup G) (hSF : pointSylow T v < F)
    (hFH : F ≤ pointJoin T v I) : 3 ∣ Nat.card F := by
  let H := pointJoin T v I
  let X := F.subgroupOf H
  obtain ⟨S,hS⟩ := c.join_sylow
  have hSX : (S : Subgroup H) ≤ X := by
    intro x hx
    exact hSF.le (hS ▸ mem_map_of_mem H.subtype hx)
  by_contra h3
  have hX3 : ¬ 3 ∣ Nat.card X := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv]
  have him3 : ¬ 3 ∣ Nat.card (X.map m.joinAction) := fun h =>
    hX3 (h.trans (card_dvd_of_surjective (m.joinAction.subgroupMap X)
      (m.joinAction.subgroupMap_surjective X)))
  have hp := BinaryLinear.FiveFlagGeometry.isPGroup_of_sylow_le_of_not_three_dvd
    (S.mapSurjective m.joinAction_surjective) (X.map m.joinAction) (map_mono hSX) him3
  have hX2 : IsPGroup 2 X :=
    (hp.comap_of_ker_isPGroup m.joinAction m.joinAction_kernel_two).to_le
      (le_comap_map m.joinAction X)
  have he := S.is_maximal' hX2 hSX
  have hh := congrArg (Subgroup.map H.subtype) he
  rw [map_subgroupOf_eq_of_le hFH,hS] at hh
  exact hSF.ne hh.symm

/-- The literal moving node fixes u precisely on its common point Sylow. -/
theorem LinearFiveData.moving_node_point_centralizer {c : Context D t v I}
    (m : LinearFiveData c) (F : Subgroup G) (hSF : pointSylow T v ⋖ F)
    (hFH : F ≤ pointJoin T v I) (hFC : ¬ F ≤ planeCentralizer T t v I) :
    F ⊓ centralizer ({oppositePoint t v} : Set G) = pointSylow T v := by
  have hSC : pointSylow T v ≤ centralizer ({oppositePoint t v} : Set G) :=
    m.pointSylow_centralizes_plane.trans (centralizer_le (Set.singleton_subset_iff.mpr
      ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))))
  rcases (covBy_iff_lt_and_eq_or_eq.mp hSF).2 _ (le_inf hSF.le hSC) inf_le_left with h | h
  · exact h
  · apply False.elim
    apply hFC
    change F ≤ pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)
    rw [c.join_plane_centralizer]
    exact le_inf hFH (h.symm.le.trans inf_le_right)

omit [Finite G] in
private theorem prime_card_elementary (X : Subgroup G) (hc : Nat.card X = 3) :
    IsElementaryAbelian 3 X := by
  let : IsCyclic X := isCyclic_of_prime_card hc
  exact { toIsMulCommutative := inferInstance
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            (fun x => by rw [←hc]; exact pow_card_eq_one') }

/-- A cubic factor in the literal moving node belongs to L and meets C_G(u) trivially. -/
theorem LinearFiveData.exists_moving_cubic {c : Context D t v I}
    (m : LinearFiveData c) (F : Subgroup G) (hSF : pointSylow T v ⋖ F)
    (hFL : F ≤ L ⊔ pointSylow T v) (hFC : ¬ F ≤ planeCentralizer T t v I) :
    ∃ X : Subgroup G, X ≤ F ∧ X ≤ L ∧ IsElementaryAbelian 3 X ∧ Nat.card X = 3 ∧
      Disjoint X (centralizer ({oppositePoint t v} : Set G)) := by
  have hFH : F ≤ pointJoin T v I := hFL.trans
    (sup_le (c.escaping.strict.le.trans le_sup_left) le_sup_right)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 3
    (m.three_dvd_sylow_overgroup F hSF.lt hFH)
  let X := zpowers (x : G)
  have hX : X ≤ F := zpowers_le.mpr x.property
  have hcX : Nat.card X = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe x,hx]
  have hpX : IsPPerfect 2 X := by
    intro N hN hp
    let _ := hN
    have hd : Nat.card (X ⧸ N) ∣ 3 := hcX ▸ N.card_quotient_dvd_card
    have hc : Nat.card (X ⧸ N) = 1 := by
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
      · exact h
      · have hdiv : 2 ∣ 3 := h ▸ (hn ▸ dvd_pow_self 2 (by
          intro hz
          simp [hz] at hn
          omega))
        omega
    exact (index_eq_one.mp hc)
  have hXL : X ≤ L := le_of_isPPerfect_of_le_sup_of_normalizes X L (pointSylow T v)
    hpX ((Chapter1.isSylowIn_iff.mp c.join_sylow).1) c.escaping.sylow_normalizes (hX.trans hFL)
  have he := m.moving_node_point_centralizer F hSF hFH hFC
  have hxs : Disjoint X (pointSylow T v) := by
    obtain ⟨n,hn⟩ := ((Chapter1.isSylowIn_iff.mp c.join_sylow).1).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hcX,hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)
  refine ⟨X,hX,hXL,prime_card_elementary X hcX,hcX,?_⟩
  apply disjoint_def.mpr
  intro z hz hzc
  exact hxs.le_bot ⟨hz,he ▸ (show z ∈ F ⊓ centralizer ({oppositePoint t v} : Set G) from ⟨hX hz,hzc⟩)⟩

/-- The actual original factors commute modulo the orbit's intrinsic two-core. -/
theorem Context.factor_commutator_le_orbit_core (c : Context D t v I) :
    ⁅L,L.map (MulAut.conj t).toMonoidHom⁆ ≤ (localOrbit T L).pCoreIn 2 := by
  have hL : L ≤ localOrbit T L := le_componentOrbit L T
  have hLt : L.map (MulAut.conj t).toMonoidHom ≤ localOrbit T L :=
    le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj s.val).toMonoidHom)
      ⟨t,c.escaping.t_mem⟩
  exact (le_inf ((commutator_mono hL hLt).trans
      (le_normalizer_iff_commutator_le_left.mp (localOrbit T L).le_normalizer))
    (source_conjugate_commutator_le_core D.simpleQTKE D.maximal.1
      c.escaping.t_mem c.escaping.t_not_normalizes)).trans
        (inf_pCoreIn_le_of_le 2 (componentOrbit_le_sup L T))

/-- The two original cubic factors lift together; the resulting nine-group
has no nonidentity element centralizing the original plane. -/
theorem LinearFiveData.exists_cubic_pair {c : Context D t v I}
    (m : LinearFiveData c) (X : Subgroup G) (hXL : X ≤ L)
    (hXe : IsElementaryAbelian 3 X) (hXc : Nat.card X = 3)
    (hXu : Disjoint X (centralizer ({oppositePoint t v} : Set G))) :
    ∃ E : Subgroup G, E ≤ X ⊔ X.map (MulAut.conj t).toMonoidHom ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      Disjoint E (centralizer (pointPlane t v : Set G)) := by
  let H := localOrbit T L
  let f := (MulAut.conj t).toMonoidHom
  let Y := X.map f
  have hXH : X ≤ H := hXL.trans (le_componentOrbit L T)
  have hYH : Y ≤ H := (map_mono hXL).trans
    (le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj s.val).toMonoidHom)
      ⟨t,c.escaping.t_mem⟩)
  have hXv : X ≤ centralizer ({v} : Set G) :=
    hXL.trans (c.escaping.strict.le.trans c.escaping.le_centralizer)
  have hYu : Y ≤ centralizer ({oppositePoint t v} : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f x * f v = f v * f x
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hXv hx))
  have hYv : Disjoint Y (centralizer ({v} : Set G)) := by
    apply disjoint_def.mpr
    rintro _ ⟨x,hx,rfl⟩ hv
    have hc : x ∈ centralizer ({oppositePoint t v} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply (MulAut.conj t).injective
      change f (x * oppositePoint t v) = f (oppositePoint t v * x)
      simpa only [map_mul,show f (oppositePoint t v) = v from m.exchange_opposite] using
        mem_centralizer_singleton_iff.mp hv
    rw [show x = 1 from hXu.le_bot ⟨hx,hc⟩,map_one]
  let A := X.subgroupOf H
  let B := Y.subgroupOf H
  let C := (centralizer ({oppositePoint t v} : Set G)).subgroupOf H
  let V := (centralizer ({v} : Set G)).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let := hXe
  let : IsElementaryAbelian 3 Y := IsElementaryAbelian.map f
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.subgroupOf hXH
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.subgroupOf hYH
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hAB : ⁅A,B⁆ ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hYH]
    exact (commutator_mono hXL (map_mono hXL)).trans c.factor_commutator_le_orbit_core
  have hcomm : A.map q ≤ centralizer (B.map q : Set (H ⧸ pCore 2 H)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hAB
  have hkerCV : q.ker ≤ C ⊓ V := by
    intro x hx
    have hxQ : (x : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype
      (show x ∈ pCore 2 H from (QuotientGroup.eq_one_iff x).mp hx)
    have hxE := (source_fullModule_orbit_core_centralizes D hxQ)
    constructor
    · exact mem_centralizer_singleton_iff.mpr
        (hxE _ (m.plane_le_fullModule (mem_sup_left (mem_zpowers _)))).symm
    · exact mem_centralizer_singleton_iff.mpr
        (hxE _ (m.plane_le_fullModule (mem_sup_right (mem_zpowers _)))).symm
  have hAc : Nat.card A = 3 := (Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv).trans hXc
  have hBc : Nat.card B = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv,card_map_of_injective (MulAut.conj t).injective,hXc]
  have hAC : Disjoint A C := by
    apply disjoint_def.mpr
    intro x hx hc
    exact Subtype.ext (hXu.le_bot ⟨hx,hc⟩)
  have hBV : Disjoint B V := by
    apply disjoint_def.mpr
    intro x hx hc
    exact Subtype.ext (hYv.le_bot ⟨hx,hc⟩)
  obtain ⟨E,hE,hEe,hEc,hEd⟩ := exists_separated_elementary_pair q hk A B C V
    hAc hBc hcomm hkerCV (comap_mono hXv) (comap_mono hYu) hAC hBV
  let := hEe
  refine ⟨E.map H.subtype,?_,IsElementaryAbelian.map H.subtype,?_,?_⟩
  · have hh := map_mono (f := H.subtype) hE
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hYH] at hh
  · simpa only [card_map_of_injective H.subtype_injective,show (3:ℕ)^2=9 from by decide] using hEc
  · apply disjoint_def.mpr
    rintro _ ⟨x,hx,rfl⟩ hc
    apply congrArg Subtype.val (hEd.le_bot ⟨hx,?_,?_⟩ : x = 1)
    · exact mem_centralizer_singleton_iff.mpr
        (hc _ (mem_sup_left (mem_zpowers _))).symm
    · exact mem_centralizer_singleton_iff.mpr
        (hc _ (mem_sup_right (mem_zpowers _))).symm

/-- The literal moving pair contains the nine-group required by the source;
its common point-centralizer intersection is trivial. -/
theorem LinearFiveData.exists_moving_nine {c : Context D t v I}
    (m : LinearFiveData c) (F : Subgroup G) (hSF : pointSylow T v ⋖ F)
    (hFL : F ≤ L ⊔ pointSylow T v) (hFC : ¬ F ≤ planeCentralizer T t v I) :
    ∃ E : Subgroup G, E ≤ F ⊔ F.map (MulAut.conj t).toMonoidHom ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      Disjoint E (centralizer (pointPlane t v : Set G)) := by
  obtain ⟨X,hXF,hXL,hXe,hXc,hXu⟩ := m.exists_moving_cubic F hSF hFL hFC
  obtain ⟨E,hE,he,hc,hd⟩ := m.exists_cubic_pair X hXL hXe hXc hXu
  exact ⟨E,hE.trans (sup_le_sup hXF (map_mono hXF)),he,hc,hd⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
