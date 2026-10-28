module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Generation
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.FirstNode

/-!
# The original first-node parabolic and its residual

The extended actor has a two-group kernel and carries the original Sylow
subgroup onto the full matrix flag group. Pulling back the first-node model
gives the literal factorizations M₁ = PL₁ and P = O²(P)T. The original P/O₂(P)
is SL₂(2), its Sylow index is three, and M₁/O₂(M₁) is SL₂(2) × SL₃(2), with
both quotient maps tied to the actual diagonal blocks.

The same maps prove Y = O²(P) = O^{3′}(P) is normal in M₁, lies in L₃ ∩ L₆,
and commutes with L₁ modulo O₂(L₁). It supplies an element outside L₁.
For i = 3,6 the actual intersections satisfy M₁ ∩ Mᵢ = PPᵢ and P ∩ Pᵢ = T,
where Pᵢ = Mᵢ ∩ L₁T. These are the parabolic inputs to the remaining local
component and ambient-normalizer arguments; those arguments remain separate.

Source: Aschbacher--Smith, notation before 12.5.3 and proof of 12.5.4,
printed pp.817--819. Final exterior assembly belongs to qt-d-1251-source.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Representation.SL5ExteriorSquare
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

omit [Finite G] in
/-- The extended actor has two-group kernel, with no ambient containment assumption. -/
theorem actor_ker_isPGroup : IsPGroup 2 s.actor.ker := by
  let H := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : N ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hq : IsPGroup 2 (H ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N _ T.isPGroup'.comap_subtype hgen
  intro k
  obtain ⟨m,hm⟩ := hq (QuotientGroup.mk' N (k : H))
  have hkm : ((k : H) ^ (2^m) : H) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N ((k : H) ^ (2^m)) = 1
    rw [map_pow]
    exact hm
  let l : L := ⟨(k : G) ^ (2^m),hkm⟩
  have hl : l ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply s.marking.quotientEquiv.injective
    change s.marking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = s.marking.quotientEquiv 1
    rw [map_one, ← s.actor_component]
    change s.actor ((k : H) ^ (2^m)) = 1
    rw [map_pow, show s.actor (k : H) = 1 from k.property, one_pow]
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)) ⟨l,hl⟩
  refine ⟨m+n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun x : pCore 2 L => ((x : L) : G)) hn
  change ((k : H) : G) ^ (2^(m+n)) = 1
  change (((k : H) : G) ^ (2^m)) ^ (2^n) = 1 at he
  simpa only [pow_add, pow_mul] using he

omit [Finite G] in
theorem actor_ker_le_sylow : s.actor.ker ≤ (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) :=
  s.actor_ker_isPGroup.le_sylow_of_normal (T.subtype le_sup_right)

theorem actor_image_sylow :
    ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map s.actor = flagGroup := by
  let S := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).mapSurjective
    s.actor_surjective
  have hS : (S : Subgroup Representation.SL5TenDimensional.Group) ≤ flagGroup := by
    rintro _ ⟨t,ht,rfl⟩
    exact s.sylow_flag ⟨t,ht⟩
  have hp : IsPGroup 2 flagGroup := by
    rw [flagGroup_eq_standardBorel_comap]
    exact BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow.isPGroup'.comap_of_injective
      _ (BinaryLinear.OuterCyclic.slEquivLinear 5).injective
  exact (S.is_maximal' hp hS).symm

theorem actor_image_Li (i : ℕ) (hi : LocalIndex i) :
    ((s.marking.Li i).subgroupOf (L ⊔ (T : Subgroup G))).map s.actor =
      parabolicResidual (localFlagDimension i) := by
  ext g
  constructor
  · rintro ⟨l,hl,rfl⟩
    have he := s.actor_component ⟨l, s.marking.Li_le_L i hl⟩
    rw [he]
    exact (s.marking.componentActor_image_Li i hi).le
      (mem_map_of_mem _ hl)
  · intro hg
    obtain ⟨l,hl,he⟩ := (s.marking.componentActor_image_Li i hi).ge hg
    refine ⟨⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩, hl, ?_⟩
    exact (s.actor_component l).trans he

theorem actor_image_local_join (i : ℕ) (hi : LocalIndex i) :
    ((s.marking.Li i ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map s.actor =
      parabolicResidualFlag (localFlagDimension i) := by
  rw [subgroupOf_sup ((s.marking.Li_le_L i).trans le_sup_left) le_sup_right,
    Subgroup.map_sup, s.actor_image_Li i hi, s.actor_image_sylow]
  rfl

theorem actor_preimage_local_join (i : ℕ) (hi : LocalIndex i) :
    (parabolicResidualFlag (localFlagDimension i)).comap s.actor =
      (s.marking.Li i ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  rw [← s.actor_image_local_join i hi, comap_map_eq]
  exact sup_eq_left.mpr (s.actor_ker_le_sylow.trans (comap_mono le_sup_right))

omit [Finite G] in
theorem mem_normalizer_subspace_join (W : Submodule (ZMod 2) Representation.SL5ExteriorSquare.V)
    (l : (L ⊔ (T : Subgroup G) : Subgroup G)) : (l : G) ∈ normalizer (s.marking.subspace W : Set G) ↔
      s.actor l ∈ Representation.SL5ExteriorSquare.exteriorStabilizer W := by
  constructor
  · intro h w
    let v := s.marking.coordinates.symm (Multiplicative.ofAdd w)
    have he := s.equivariant l v
    have hm := (mem_normalizer_iff.mp h (v : G))
    rw [s.marking.mem_subspace W v, s.marking.mem_subspace W
      ⟨(l : G) * (v : G) * (l : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes l.property) (v : G)).mp v.property⟩] at hm
    change Representation.SL5TenDimensional.exteriorAction 2
      (s.actor l) w ∈ W ↔ w ∈ W
    simpa only [he, v, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hm.symm
  · intro h
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      have hxV := s.marking.subspace_le W hx
      have he := s.equivariant l ⟨x, hxV⟩
      apply (s.marking.mem_subspace W ⟨(l : G) * x * (l : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes l.property) x).mp hxV⟩).mpr
      rw [he]
      exact (h _).mpr ((s.marking.mem_subspace W ⟨x, hxV⟩).mp hx)
    · intro hx
      have hxV : x ∈ V := (mem_normalizer_iff.mp (s.normalizes l.property) x).mpr
        (s.marking.subspace_le W hx)
      have he := s.equivariant l ⟨x, hxV⟩
      apply (s.marking.mem_subspace W ⟨x, hxV⟩).mpr
      apply (h _).mp
      have hm := (s.marking.mem_subspace W ⟨(l : G) * x * (l : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes l.property) x).mp hxV⟩).mp hx
      rwa [he] at hm

omit [Finite G] in
theorem mem_Gi_iff_join_actor (i : ℕ) (hi : LocalIndex i)
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    (x : G) ∈ s.marking.Gi i ↔ s.actor x ∈ parabolic (localFlagDimension i) := by
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [ExteriorMarking.Gi, ExteriorMarking.Vi, localFlagDimension,
      ← exteriorStabilizer_V₁_eq_parabolic] using s.mem_normalizer_subspace_join V₁ x
  · simpa only [ExteriorMarking.Gi, ExteriorMarking.Vi, localFlagDimension,
      ← exteriorStabilizer_V₃_eq_parabolic] using s.mem_normalizer_subspace_join V₃ x
  · simpa only [ExteriorMarking.Gi, ExteriorMarking.Vi, localFlagDimension,
      ← exteriorStabilizer_V₄_eq_parabolic] using s.mem_normalizer_subspace_join V₄ x
  · simpa only [ExteriorMarking.Gi, ExteriorMarking.Vi, localFlagDimension,
      ← exteriorStabilizer_V₆_eq_parabolic] using s.mem_normalizer_subspace_join V₆ x

omit [Finite G] in
theorem Mi_eq_actor_preimage (i : ℕ) (hi : LocalIndex i) :
    s.marking.Mi i = ((parabolic (localFlagDimension i)).comap s.actor).map
      (L ⊔ (T : Subgroup G)).subtype := by
  apply le_antisymm
  · intro x hx
    exact ⟨⟨x,hx.1⟩, (s.mem_Gi_iff_join_actor i hi ⟨x,hx.1⟩).mp hx.2, rfl⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨x.property, (s.mem_Gi_iff_join_actor i hi x).mpr hx⟩

/-- The full flag subgroup lifts back to the original Sylow subgroup. -/
theorem actor_preimage_flag : flagGroup.comap s.actor =
    (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) := by
  rw [← s.actor_image_sylow, comap_map_eq, sup_eq_left.mpr s.actor_ker_le_sylow]

omit [Finite G] in
theorem mem_P_iff_actor (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    (x : G) ∈ s.P ↔ s.actor x ∈ firstNodeParabolic :=
  mem_map_iff_mem (L ⊔ (T : Subgroup G)).subtype_injective

/-- The source first node lies in each of the two relevant residual Sylow joins. -/
theorem P_le_local_join (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.P ≤ s.marking.Li i ⊔ (T : Subgroup G) := by
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hm : firstNodeParabolic ≤ parabolicResidualFlag (localFlagDimension i) := by
    rcases hi with rfl | rfl
    · exact firstNode_le_threeResidualFlag
    · exact firstNode_le_fourResidualFlag
  rintro _ ⟨x,hx,rfl⟩
  have hh : x ∈ (parabolicResidualFlag (localFlagDimension i)).comap s.actor := hm hx
  rw [s.actor_preimage_local_join i hidx] at hh
  exact hh

/-- The actual first-node two-residual lies in L₃ and L₆. -/
theorem Y_le_local_residual (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.Y ≤ s.marking.Li i := by
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hp : IsPPerfect 2 (s.marking.Li i) := by
    let := s.marking.Li_perfect i
    intro N hn hq
    let := hn
    by_contra hne
    let : Nontrivial (s.marking.Li i ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (s.marking.Li i ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (s.marking.Li i ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (s.marking.Li i ⧸ N) inferInstance
  have he := embedded_pResidual_join_pGroup (s.marking.Li i) (T : Subgroup G)
    hp T.isPGroup' (s.sylow_normalizes_Li i hidx)
  exact (embedded_pResidual_mono 2 (s.P_le_local_join i hi)).trans he.le

/-- The literal residual used in 12.5.3--4 has both required ambient containments. -/
theorem Y_le_three_inf_six : s.Y ≤ s.marking.Li 3 ⊓ s.marking.Li 6 :=
  le_inf (s.Y_le_local_residual 3 (Or.inl rfl)) (s.Y_le_local_residual 6 (Or.inr rfl))

/-- The first-node parabolic and the point residual generate the original M₁. -/
theorem M₁_eq_P_sup_point_residual : s.marking.Mi 1 = s.P ⊔ s.marking.Li 1 := by
  let H := L ⊔ (T : Subgroup G)
  rw [s.Mi_eq_actor_preimage 1 (Or.inl rfl)]
  change ((parabolic 2).comap s.actor).map H.subtype = _
  rw [← firstNode_sup_pointResidual, ← comap_sup_eq _ _ _ s.actor_surjective, Subgroup.map_sup]
  change s.P ⊔ ((parabolicResidual (localFlagDimension 1)).comap s.actor).map H.subtype = _
  rw [← s.actor_image_Li 1 (Or.inl rfl), comap_map_eq, Subgroup.map_sup,
    map_subgroupOf_eq_of_le ((s.marking.Li_le_L 1).trans le_sup_left), ← sup_assoc]
  apply sup_eq_left.mpr
  rintro _ ⟨x,hx,rfl⟩
  exact (le_sup_left : s.P ≤ s.P ⊔ s.marking.Li 1)
    (s.sylow_le_P (s.actor_ker_le_sylow hx))

/-- The original Sylow subgroup supplements the literal two-residual of P. -/
theorem P_eq_Y_sup_sylow : s.P = s.Y ⊔ (T : Subgroup G) := by
  have he := congrArg (map s.P.subtype) (pResidual_sup_sylow_eq_top (T.subtype s.sylow_le_P))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le s.sylow_le_P,
    ← MonoidHom.range_eq_map, range_subtype, Y] using he.symm

/-- The complete source point normalizer is generated by Y, L₁ and T. -/
theorem M₁_eq_Y_sup_point_residual_sup_sylow :
    s.marking.Mi 1 = s.Y ⊔ s.marking.Li 1 ⊔ (T : Subgroup G) := by
  rw [s.M₁_eq_P_sup_point_residual, s.P_eq_Y_sup_sylow]
  ac_rfl

/-- P is the first node omitted by L₁T, in the literal ambient group. -/
theorem P_not_le_point_residual_join : ¬ s.P ≤ s.marking.Li 1 ⊔ (T : Subgroup G) := by
  intro hh
  apply firstNode_not_le_pointResidualFlag
  intro g hg
  obtain ⟨x,rfl⟩ := s.actor_surjective g
  have hx := hh ((s.mem_P_iff_actor x).mpr hg)
  have hxm : x ∈ (s.marking.Li 1 ⊔ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G)) := hx
  rw [← s.actor_preimage_local_join 1 (Or.inl rfl)] at hxm
  exact hxm

/-- The actual two-residual supplies an element outside the point residual. -/
theorem Y_not_le_point_residual : ¬ s.Y ≤ s.marking.Li 1 := by
  intro hh
  apply s.P_not_le_point_residual_join
  rw [s.P_eq_Y_sup_sylow]
  exact sup_le_sup hh le_rfl

/-- Restriction of the original LT actor to the first-node parabolic. -/
noncomputable def PActor : s.P →* firstNodeParabolic :=
  (s.actor.comp (inclusion (s.P_le_M₁.trans inf_le_left))).codRestrict _
    (fun x => (s.mem_P_iff_actor _).mp x.property)

omit [Finite G] in
theorem PActor_surjective : Function.Surjective s.PActor := by
  intro g
  obtain ⟨x,hx⟩ := s.actor_surjective g.val
  exact ⟨⟨x,(s.mem_P_iff_actor x).mpr (hx ▸ g.property)⟩, Subtype.ext hx⟩

omit [Finite G] in
theorem PActor_ker_isPGroup : IsPGroup 2 s.PActor.ker := by
  have he : s.PActor.ker = s.actor.ker.comap (inclusion (s.P_le_M₁.trans inf_le_left)) := by
    ext x
    change s.PActor x = 1 ↔ s.actor (inclusion _ x) = 1
    exact Subtype.ext_iff
  rw [he]
  exact s.actor_ker_isPGroup.comap_of_injective _ (inclusion_injective _)

noncomputable def PCoreEquiv : (s.P ⧸ pCore 2 s.P) ≃*
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ((s.PActor).pCoreQuotientEquiv s.PActor_surjective s.PActor_ker_isPGroup).trans
    firstNodeQuotientEquiv

/-- The quotient marking retains the actual first two-coordinate block. -/
theorem PCoreEquiv_mk (p : s.P) :
    s.PCoreEquiv (QuotientGroup.mk' _ p) = firstNodeSmallHom (s.PActor p) := rfl

/-- Restriction of the extended actor to the literal normalizer in LT. -/
noncomputable def localJoinActor (i : ℕ) (hi : LocalIndex i) :
    s.marking.Mi i →* parabolic (localFlagDimension i) :=
  (s.actor.comp (inclusion inf_le_left)).codRestrict _
    (fun x => (s.mem_Gi_iff_join_actor i hi ⟨x,x.property.1⟩).mp x.property.2)

omit [Finite G] in
theorem localJoinActor_surjective (i : ℕ) (hi : LocalIndex i) :
    Function.Surjective (s.localJoinActor i hi) := by
  intro g
  obtain ⟨x,hx⟩ := s.actor_surjective g.val
  exact ⟨⟨x,x.property,(s.mem_Gi_iff_join_actor i hi x).mpr (hx ▸ g.property)⟩, Subtype.ext hx⟩

omit [Finite G] in
theorem localJoinActor_ker_isPGroup (i : ℕ) (hi : LocalIndex i) :
    IsPGroup 2 (s.localJoinActor i hi).ker := by
  have he : (s.localJoinActor i hi).ker = s.actor.ker.comap (inclusion inf_le_left) := by
    ext x
    change s.localJoinActor i hi x = 1 ↔ s.actor (inclusion inf_le_left x) = 1
    exact Subtype.ext_iff
  rw [he]
  exact s.actor_ker_isPGroup.comap_of_injective _ (inclusion_injective _)

/-- The actual point normalizer's quotient, in original diagonal-block order. -/
noncomputable def M₁CoreEquiv : (s.marking.Mi 1 ⧸ pCore 2 (s.marking.Mi 1)) ≃*
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  ((s.localJoinActor 1 (Or.inl rfl)).pCoreQuotientEquiv
    (s.localJoinActor_surjective 1 (Or.inl rfl))
    (s.localJoinActor_ker_isPGroup 1 (Or.inl rfl))).trans parabolicTwoQuotientEquiv

theorem M₁CoreEquiv_mk (m : s.marking.Mi 1) :
    s.M₁CoreEquiv (QuotientGroup.mk' _ m) =
      parabolicLeviHom 2 (by decide) (s.localJoinActor 1 (Or.inl rfl) m) := rfl

omit [Finite G] in
/-- The original LT normalizer normalizes its literal local residual. -/
theorem Mi_normalizes_Li (i : ℕ) :
    s.marking.Mi i ≤ normalizer (s.marking.Li i : Set G) := by
  have hLT : (L ⊔ (T : Subgroup G) : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hn : s.marking.Mi i ≤ normalizer (L ⊓ s.marking.Gi i : Set G) :=
    (le_inf (inf_le_left.trans hLT)
      (inf_le_right.trans (s.marking.Gi i).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (L ⊓ s.marking.Gi i) (solvableResidual (L ⊓ s.marking.Gi i : Subgroup G)))

omit [Finite G] in
theorem Li_le_Mi (i : ℕ) : s.marking.Li i ≤ s.marking.Mi i :=
  le_inf ((s.marking.Li_le_L i).trans le_sup_left) (s.marking.Li_le_Gi i)

/-- The first node has no large-block action in its two-residual. -/
theorem Y_point_large_block (y : s.P) (hy : y ∈ pResidual 2 s.P) :
    (s.M₁CoreEquiv (QuotientGroup.mk' _ (inclusion s.P_le_M₁ y))).2 = 1 := by
  have hm := firstNode_residual_large_block (s.PActor y)
    ((map_pResidual_le 2 s.PActor) (mem_map_of_mem s.PActor hy))
  exact hm

/-- The point residual has identity small block in the original M₁ quotient. -/
theorem point_residual_small_block (l : s.marking.Li 1) :
    (s.M₁CoreEquiv (QuotientGroup.mk' _ (inclusion (s.Li_le_Mi 1) l))).1 = 1 := by
  let x : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨l,(s.marking.Li_le_L 1).trans le_sup_left l.property⟩
  have hm : s.actor x ∈ parabolicResidual 2 := by
    exact (s.actor_image_Li 1 (Or.inl rfl)).le (mem_map_of_mem _ l.property)
  rw [parabolicResidual_two] at hm
  have hh : ((s.localJoinActor 1 (Or.inl rfl) (inclusion (s.Li_le_Mi 1) l)) :
      parabolic 2).val ∈ parabolicTwoSmallBlock.ker.map (parabolic 2).subtype := hm
  exact (mem_map_iff_mem (f := (parabolic 2).subtype)
    (parabolic 2).subtype_injective (K := parabolicTwoSmallBlock.ker)
    (x := s.localJoinActor 1 (Or.inl rfl) (inclusion (s.Li_le_Mi 1) l))).mp hh

/-- The two original factors commute modulo the point-normalizer two-core. -/
theorem Y_point_commutator_le_M₁_core :
    ⁅s.Y, s.marking.Li 1⁆ ≤ (s.marking.Mi 1).pCoreIn 2 := by
  let H := s.marking.Mi 1
  let f : H →* (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    s.M₁CoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ s.M₁CoreEquiv.injective,
      QuotientGroup.ker_mk']
  apply commutator_le.mpr
  rintro y ⟨yP,hy,rfl⟩ l hl
  let yH : H := inclusion s.P_le_M₁ yP
  let lH : H := inclusion (s.Li_le_Mi 1) ⟨l,hl⟩
  have hy2 : (f yH).2 = 1 := s.Y_point_large_block yP hy
  have hl1 : (f lH).1 = 1 := s.point_residual_small_block ⟨l,hl⟩
  refine ⟨⁅yH,lH⁆, ?_, rfl⟩
  rw [← hk]
  change f ⁅yH,lH⁆ = 1
  rw [map_commutatorElement]
  apply Prod.ext
  · change ⁅(f yH).1,(f lH).1⁆ = 1
    simp only [hl1, commutatorElement_def, mul_one, inv_one, mul_inv_cancel]
  · change ⁅(f yH).2,(f lH).2⁆ = 1
    simp only [hy2, commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]

/-- The source commutator lies in the two-core of L₁ itself. -/
theorem Y_point_commutator_le_point_core :
    ⁅s.Y, s.marking.Li 1⁆ ≤ (s.marking.Li 1).pCoreIn 2 := by
  let H := s.marking.Mi 1
  let B := s.marking.Li 1
  let j : B →* H := inclusion (s.Li_le_Mi 1)
  have hp : (pCore 2 H).comap j ≤ pCore 2 B :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective j (inclusion_injective _)⟩
  have hYH : s.Y ≤ H := (map_subtype_le _).trans s.P_le_M₁
  have hcom : ⁅s.Y,B⁆ ≤ B :=
    (le_normalizer_iff_commutator_le_right).mp (hYH.trans (s.Mi_normalizes_Li 1))
  intro x hx
  have hxB := hcom hx
  obtain ⟨xH,hxH,hxe⟩ := s.Y_point_commutator_le_M₁_core hx
  refine ⟨⟨x,hxB⟩,hp ?_,rfl⟩
  change j ⟨x,hxB⟩ ∈ pCore 2 H
  exact (show xH = j ⟨x,hxB⟩ from Subtype.ext hxe) ▸ hxH

/-- The common three- and six-space residual contains an element outside L₁. -/
theorem exists_common_residual_outside_point :
    ∃ y ∈ s.Y, y ∈ s.marking.Li 3 ∧ y ∈ s.marking.Li 6 ∧ y ∉ s.marking.Li 1 := by
  obtain ⟨y,hy,hout⟩ := SetLike.not_le_iff_exists.mp s.Y_not_le_point_residual
  exact ⟨y,hy,(s.Y_le_three_inf_six hy).1,(s.Y_le_three_inf_six hy).2,hout⟩

/-- The actual Y = O²(P) is normal in M₁, as asserted before 12.5.3. -/
theorem Y_normal_in_M₁ : (s.Y.subgroupOf (s.marking.Mi 1)).Normal := by
  let H := s.marking.Mi 1
  let A := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  let B := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  let f : H →* A × B := s.M₁CoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let q := QuotientGroup.mk' (pResidual 2 A)
  let g : H →* (A ⧸ pResidual 2 A) × B :=
    ((q.comp (MonoidHom.fst A B)).prod (MonoidHom.snd A B)).comp f
  let N := g.ker.map H.subtype
  have hNP : N ≤ s.P := by
    rintro _ ⟨m,hm,rfl⟩
    have he : (f m).2 = 1 := congrArg Prod.snd (show g m = 1 from hm)
    apply (s.mem_P_iff_actor ⟨m,m.property.1⟩).mpr
    apply (mem_firstNode_iff_large_upper (s.localJoinActor 1 (Or.inl rfl) m)).mpr
    change (f m).2.val.IsUpperTriangular
    rw [he]
    exact Matrix.blockTriangular_one
  have hYN : s.Y ≤ N := by
    rintro _ ⟨p,hp,rfl⟩
    refine ⟨inclusion s.P_le_M₁ p, ?_, rfl⟩
    change g (inclusion s.P_le_M₁ p) = 1
    apply Prod.ext
    · apply (QuotientGroup.eq_one_iff _).mpr
      let a := firstNodeSmallHom.comp s.PActor
      exact (map_pResidual_le 2 a) (mem_map_of_mem a hp)
    · exact s.Y_point_large_block p hp
  have he : (pResidual 2 N).map N.subtype = s.Y :=
    embedded_pResidual_eq_of_le_of_residual_le 2 hNP hYN
  have hn : (N.subgroupOf H).Normal := by
    change ((g.ker.map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hres := normal_embedded_pResidual_subgroupOf 2 (show N ≤ H from map_subtype_le _) hn
  rwa [he] at hres

/-- The source residual product commutator is contained in both original factors. -/
theorem Y_point_commutator_le_intersection :
    ⁅s.Y, s.marking.Li 1⁆ ≤ s.Y ⊓ (s.marking.Li 1).pCoreIn 2 := by
  have hYH : s.Y ≤ s.marking.Mi 1 := (map_subtype_le _).trans s.P_le_M₁
  have hn := (normal_subgroupOf_iff_le_normalizer hYH).mp s.Y_normal_in_M₁
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp ((s.Li_le_Mi 1).trans hn))
    s.Y_point_commutator_le_point_core

/-- The source's two residual notations agree on the original P. -/
theorem Y_eq_primeToThree : s.Y = (primeToResidual 3 s.P).map s.P.subtype := by
  exact congrArg (map s.P.subtype)
    (twoResidual_eq_primeToResidual_three_of_two_kernel s.PActor s.PActor_surjective
      s.PActor_ker_isPGroup firstNode_twoResidual_eq_primeToThree)

/-- The chosen Sylow has index three in the actual first-node parabolic. -/
theorem sylow_relIndex_P : (T : Subgroup G).relIndex s.P = 3 := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact SymmetricThreeTwoCore.sylow_index_three (s.PCoreEquiv.trans e) (T.subtype s.sylow_le_P)

/-- The original Sylow is self-normalizing inside this minimal parabolic. -/
theorem sylow_self_normalizing_in_P :
    normalizer ((T : Subgroup G).subgroupOf s.P : Set s.P) =
      (T : Subgroup G).subgroupOf s.P := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact SymmetricThreeTwoCore.sylow_self_normalizing (s.PCoreEquiv.trans e) (T.subtype s.sylow_le_P)

/-- The original first node and L₁T intersect precisely in T. -/
theorem P_inf_point_residual_join :
    s.P ⊓ (s.marking.Li 1 ⊔ (T : Subgroup G)) = (T : Subgroup G) := by
  apply le_antisymm
  · rintro x ⟨hxP,hxR⟩
    let xH : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨x,(s.P_le_M₁ hxP).1⟩
    have hr : s.actor xH ∈ parabolicResidualFlag 2 := by
      have hh : xH ∈ (s.marking.Li 1 ⊔ (T : Subgroup G)).subgroupOf
          (L ⊔ (T : Subgroup G)) := hxR
      rwa [← s.actor_preimage_local_join 1 (Or.inl rfl)] at hh
    have hf : xH ∈ flagGroup.comap s.actor :=
      firstNode_inf_pointResidualFlag.le ⟨(s.mem_P_iff_actor xH).mp hxP,hr⟩
    rw [s.actor_preimage_flag] at hf
    exact hf
  · exact le_inf s.sylow_le_P le_sup_right

/-- The other parabolic at the intersection in the source notation. -/
noncomputable def Pi (i : ℕ) : Subgroup G :=
  s.marking.Mi i ⊓ (s.marking.Li 1 ⊔ (T : Subgroup G))

/-- The first-node subgroup lies in each relevant normalizer inside LT. -/
theorem P_le_Mi (i : ℕ) (hi : i = 3 ∨ i = 6) : s.P ≤ s.marking.Mi i := by
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  exact le_inf (s.P_le_M₁.trans inf_le_left)
    ((s.P_le_local_join i hi).trans (s.Li_join_sylow_le_Gi i hidx))

omit [Finite G] in
theorem Pi_le_M₁ (i : ℕ) : s.Pi i ≤ s.marking.Mi 1 := by
  exact inf_le_right.trans (sup_le (s.Li_le_Mi 1)
    (le_inf le_sup_right s.sylow_le_G₁))

/-- The source factorization M₁ ∩ Mᵢ = P Pᵢ, with actual elements. -/
theorem M₁_intersection_factorization (i : ℕ) (hi : i = 3 ∨ i = 6)
    (x : G) (hx : x ∈ s.marking.Mi 1 ⊓ s.marking.Mi i) :
    ∃ p ∈ s.P, ∃ b ∈ s.Pi i, p * b = x := by
  have hPnorm := s.P_le_M₁.trans (s.Mi_normalizes_Li 1)
  have hmem : x ∈ (s.P : Set G) * (s.marking.Li 1 : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hPnorm, ← s.M₁_eq_P_sup_point_residual]
    exact hx.1
  obtain ⟨p,hp,b,hb,he⟩ := Set.mem_mul.mp hmem
  have hbMi : b ∈ s.marking.Mi i := by
    have hh := (s.marking.Mi i).mul_mem
      ((s.marking.Mi i).inv_mem (s.P_le_Mi i hi hp)) hx.2
    simpa only [← he, inv_mul_cancel_left] using hh
  exact ⟨p,hp,b,⟨hbMi,(le_sup_left : s.marking.Li 1 ≤ s.marking.Li 1 ⊔ (T : Subgroup G)) hb⟩,he⟩

/-- The same literal intersection as a subgroup join, for component consumers. -/
theorem M₁_inf_Mi_eq_P_sup_Pi (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.marking.Mi 1 ⊓ s.marking.Mi i = s.P ⊔ s.Pi i := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p,hp,b,hb,rfl⟩ := s.M₁_intersection_factorization i hi x hx
    exact mul_mem_sup hp hb
  · exact sup_le (le_inf s.P_le_M₁ (s.P_le_Mi i hi))
      (le_inf (s.Pi_le_M₁ i) inf_le_left)

/-- The two source parabolics meet in the same original Sylow subgroup. -/
theorem P_inf_Pi (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.P ⊓ s.Pi i = (T : Subgroup G) := by
  change s.P ⊓ (s.marking.Mi i ⊓ (s.marking.Li 1 ⊔ (T : Subgroup G))) = _
  rw [← inf_assoc, inf_eq_left.mpr (s.P_le_Mi i hi), s.P_inf_point_residual_join]

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
