module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.PointNode
public import Theory.Representation.BinaryConjugationSection.NormalizerAction

/-!
# The source exchange fixes an escaping minimal parabolic

The crossed component centralizes the original natural three-space. Extend
its natural coordinates to the full normalizer: the conjugate of Pc has
two-group image, while C_L(u) maps onto a vector stabilizer of order 24.
Thus the original exchange moves Pc. It exchanges two of the three nodes
inside M and fixes the unique escaping node. Transport through the actual
point-join inclusion gives a genuine minimal parabolic, including relative
nonnormality of the prescribed Sylow subgroup.

This discharges the Pc premises of Parabolic.Exchange on LinearFiveData.
The earlier model reduction and the two terminal contradictions remain
with qt-d-10-nona5-point-constrained; no exclusion theorem is asserted here.

Source: Aschbacher--Smith, 10.2.9, printed p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem natural_coordinates_injective {c : Context D t v I} (m : LinearFiveData c) :
    Function.Injective m.natural.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [m.natural.kernel_eq,bot_subgroupOf]

private def normalizerQuotient {c : Context D t v I} (m : LinearFiveData c) :
    normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) →* SL(3,ZMod 2) :=
  (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
    (BinaryConjugationSection.normalizerAction m.natural.coordinates
      ⟨natural_coordinates_injective m,m.natural.onto⟩)

private theorem normalizerQuotient_restrict {c : Context D t v I} (m : LinearFiveData c)
    (l : L) : normalizerQuotient m ⟨(l : G),m.natural.normalized l.property⟩ =
      m.quotient (QuotientGroup.mk' (pCore 2 L) l) := by
  apply (BinaryLinear.OuterCyclic.slEquivLinear 3).injective
  change (BinaryLinear.OuterCyclic.slEquivLinear 3)
    ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  apply LinearEquiv.toLinearMap_injective
  exact BinaryConjugationSection.normalizerAction_restrict m.natural
    (natural_coordinates_injective m) l

private theorem normalizerQuotient_centralizer {c : Context D t v I} (m : LinearFiveData c)
    (g : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hc : (g : G) ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    normalizerQuotient m g = 1 := by
  apply (BinaryLinear.OuterCyclic.slEquivLinear 3).injective
  change (BinaryLinear.OuterCyclic.slEquivLinear 3)
    ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm _) = _
  rw [MulEquiv.apply_symm_apply,map_one]
  apply LinearEquiv.ext
  intro w
  change BinaryConjugationSection.normalizerAction m.natural.coordinates
    ⟨natural_coordinates_injective m,m.natural.onto⟩ g w = w
  obtain ⟨a,ha⟩ := m.natural.onto (Multiplicative.ofAdd w)
  have hw : (m.natural.coordinates a).toAdd = w := congrArg Multiplicative.toAdd ha
  rw [←hw]
  have he : (⁅D.fullModule,L⁆ : Subgroup G).normalizerMonoidHom g a = a := by
    apply Subtype.ext
    change (g : G)*(a : G)*(g : G)⁻¹ = a
    rw [←hc a a.property,mul_inv_cancel_right]
  exact (BinaryConjugationSection.normalizerAction_coordinates m.natural.coordinates
    ⟨natural_coordinates_injective m,m.natural.onto⟩ g a).trans
      (congrArg (fun x => (m.natural.coordinates x).toAdd) he)

/-- The crossed component centralizes the original natural factor. -/
theorem LinearFiveData.conjugate_component_centralizes_moved {c : Context D t v I}
    (m : LinearFiveData c) :
    L.map (MulAut.conj t).toMonoidHom ≤ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W : Subgroup G := ⁅D.fullModule,L⁆
  have hn : t^2 ∈ normalizer (W : Set G) :=
    source_moved_normalizer_local_containment D
      ⟨le_normalizer_componentOrbit L T ((T : Subgroup G).pow_mem c.escaping.t_mem 2),
        c.escaping.sylow_normalizes m.exchange_square_mem⟩
  have he : (W.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = W := by
    rw [map_map]
    have hh : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (t^2)).toMonoidHom := by
      ext x
      change t*(t*x*t⁻¹)*t⁻¹ = t^2*x*(t^2)⁻¹
      simp only [pow_two]
      group
    rw [hh]
    exact mem_normalizer_iff_map_conj_eq.mp hn
  rintro _ ⟨l,hl,rfl⟩ w hw
  obtain ⟨a,ha,haw⟩ := show w ∈ (W.map (MulAut.conj t).toMonoidHom).map
    (MulAut.conj t).toMonoidHom from he.symm ▸ hw
  have hc := c.escaping.crossed ha l hl
  rw [←haw]
  change (MulAut.conj t) a * (MulAut.conj t) l =
    (MulAut.conj t) l * (MulAut.conj t) a
  rw [←map_mul,←map_mul,hc]


/-- The original component point node is moved by the exchange. -/
theorem LinearFiveData.componentPointNode_moved {c : Context D t v I}
    (m : LinearFiveData c) :
    (componentPointNode T L t v).map (MulAut.conj t).toMonoidHom ≠
      componentPointNode T L t v := by
  let W : Subgroup G := ⁅D.fullModule,L⁆
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
    exact source_moved_normalizer_local_containment D
      ⟨le_normalizer_componentOrbit L T hs.1,c.escaping.sylow_normalizes hs⟩
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
theorem LinearFiveData.exists_exchange_fixed_minimalParabolic {c : Context D t v I}
    (m : LinearFiveData c) :
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
