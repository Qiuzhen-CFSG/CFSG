module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Coordinates

/-!
# Marked spanning and rank-three disjointness in 14.7.70

The universal natural cover maps directly onto the original descended action
on U/V₁, compatibly with the original projection p. No chart from the
contradiction branch of 14.7.69 is used. Earlier R₁ centralization fixes the
literal V/V₁ image; its genuine cubic L₁ actor has invertible displacement
there. The published coordinate formula therefore identifies that image
with the marked line (0,x,0), rather than merely an arbitrary complement.

For a nonidentity upper actor the displacement vectors are (t²y,ty,0).
Together with the marked line they span all (r,x,0). If primeRank 2 U₀ = 3,
the actual identity |U₀| = 2 |ker p| forces dim(ker p) = 2; hence this same
universal-cover surjection is injective. Its displacement line then meets
the marked line trivially. The order-two commutator-image theorem transfers
both calculations to the literal [U,Uα], for any qualifying critical path.

`commutator_products` applies `commutator_sup_seed` and constructs descent
from the literal O₂(H)-centralization. `rank_three_geometry` applies the
published opening commutators and `point_not_le_seed`, using the literal
14.7.68(1) input through `point_not_le_U₀`. Neither spanning, disjointness,
nor the V-line identification is an input to these applications.

The explicit `UpperMarking` and `LocalActors` retain the compatible earlier
14.7.65 and 14.3.3(6) actor data, with producers qt-14-03 and qt-14-07.
Module separation is 14.7.2(1), owned by qt-14-07-solvable; core action is
14.5.15(4), owned by qt-14-05. The literal earlier39/F.9 inputs retain the
qt-14-07 owner. The68 and69 producers are respectively
qt-14-07-critical-residual-fusion and qt-14-07-critical-order-two.
Permitted rechoice and final preparation assembly remain with
qt-14-07-rechoice-preparation; this module proves its marked calculations.

The cubic-line argument adapts the checked `MarkedPartitions.Seed` proof;
only the independent published `MarkedPartitions.Coordinates` module is
imported. Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Remark 14.7.64, Lemma 14.7.65 and proof of 14.7.70,
printed pp.1069–1070, 1073–1074 (PDF pp.1086–1087, 1090–1091).
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
open Subgroup Representation Chapter12.Section08
open Representation.SL2FourNatural Representation.SL2FourCentralCover
open Matrix.SpecialLinearGroup MarkedPartitions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

/-- Earlier local actions with the same quotient marking as `UpperMarking`.
The producers are qt-14-03 and qt-14-07; neither premise identifies a V-line. -/
structure LocalActors : Prop where
  seed_fixed : ∀ r : F.H, (r : G) ∈ F.Ri L 1 → ∀ v : F.U, (v : G) ∈ V →
    d.action r (d.conjugationSection.coordinates v).toAdd =
      (d.conjugationSection.coordinates v).toAdd
  cubic : ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧ ∃ a : SL2FourNatural.F,
    ∃ ha : a ≠ 0, a ≠ 1 ∧
      d.qH l = alternatingActor d.naturalQuotient (diag2 a ha)

private theorem exists_cover (s : d.ActionDescent) :
    ∃ q : binaryAction.IntertwiningMap (s.action.comp (alternatingActor d.naturalQuotient)),
      Function.Surjective q ∧ ∀ w, d.projection (q w) = projection w := by
  let := finite_original d
  let p := restrictedProjection d.naturalQuotient s.projection
  exact exists_quotient p (isCover_of_natural_indecomposable p d.projection_onto
    s.kernel_fixed s.indecomposable)

/-- Universal-cover map on the original descended action and original projection. -/
def cover (s : d.ActionDescent) :
    binaryAction.IntertwiningMap (s.action.comp (alternatingActor d.naturalQuotient)) :=
  (exists_cover d s).choose

theorem cover_onto (s : d.ActionDescent) : Function.Surjective (cover d s) :=
  (exists_cover d s).choose_spec.1

theorem cover_projection (s : d.ActionDescent) (w : Space) :
    d.projection (cover d s w) = projection w := (exists_cover d s).choose_spec.2 w

variable (s : d.ActionDescent)

theorem actor_cover (h : F.H) (g : SL)
    (hh : d.qH h = alternatingActor d.naturalQuotient g) (w : Space) :
    d.action h (cover d s w) = cover d s (binaryAction g w) := by
  rw [(cover d s).isIntertwining]
  change d.action h (cover d s w) = s.action (alternatingActor d.naturalQuotient g) _
  rw [← hh, s.original]

theorem mem_upper_iff (w : W) :
    w ∈ SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) ↔
      d.projection w 1 = 0 := by
  let p := restrictedProjection d.naturalQuotient s.projection
  exact SL2CentralExtension.mem_upperFixed_iff _ p.toLinearMap d.projection_onto
    (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v)
    (fun v hv g => s.kernel_fixed hv g) w

theorem mem_upper_iff_point (w : W) :
    w ∈ SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) ↔
      ∃ r x : SL2FourNatural.F, cover d s (point r x) = w := by
  rw [mem_upper_iff]
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := cover_onto d s w
    rw [cover_projection] at hw
    exact ⟨(coordinates v).1, (coordinates v).2 0,
      congrArg (cover d s) (fixed_point v hw).symm⟩
  · rintro ⟨r, x, rfl⟩
    rw [cover_projection, point_projection]
    rfl

theorem seed_le_upper (mark : UpperMarking d) (actors : LocalActors d) :
    tilde d V ≤ SL2CentralExtension.upperFixed
      (s.action.comp (alternatingActor d.naturalQuotient)) := by
  intro w hw g
  obtain ⟨v, hv, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  have hm : alternatingActor d.naturalQuotient g ∈
      ((F.Ri L 1).subgroupOf F.H).map d.qH := by
    rw [mark]
    exact mem_map_of_mem _ g.property
  obtain ⟨r, hr, he⟩ := hm
  change s.action (alternatingActor d.naturalQuotient g) _ = _
  rw [← he, s.original]
  exact actors.seed_fixed r hr v hv

private theorem seed_invariant (l : F.H) (hl : (l : G) ∈ F.Li L 1)
    (w : W) (hw : w ∈ tilde d V) : d.action l w ∈ tilde d V := by
  obtain ⟨v, hv, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  have hv' : (l : G) * v * (l : G)⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (d.natural.chosen.normalizes ((F.Li_le L 1 hl).1)) v).mp hv
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr
    ⟨⟨_, Data.V_le_U F hv'⟩, hv', d.conjugationSection.equivariant l v⟩

theorem cubic_displacement (l : F.H) (a : SL2FourNatural.F) (ha : a ≠ 0)
    (he : d.qH l = alternatingActor d.naturalQuotient (diag2 a ha))
    (r x : SL2FourNatural.F) :
    d.action l (cover d s (point r x)) - cover d s (point r x) =
      cover d s (point 0 ((a - 1) * x)) := by
  rw [actor_cover d s l (diag2 a ha) he, ← map_sub, diagonal_displacement_point]

include s in
/-- The cubic displacement is onto the literal V/V₁, by separation and its L₁ action. -/
theorem cubic_seed_range (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (l : F.H) (hl : (l : G) ∈ F.Li L 1)
    (a : SL2FourNatural.F) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (he : d.qH l = alternatingActor d.naturalQuotient (diag2 a ha)) :
    ((d.action l - LinearMap.id).comp (tilde d V).subtype).range = tilde d V := by
  let := finite_original d
  let f : tilde d V →ₗ[ZMod 2] tilde d V :=
    ((d.action l - LinearMap.id).comp (tilde d V).subtype).codRestrict (tilde d V)
      (fun w => (tilde d V).sub_mem (seed_invariant d l hl w w.property) w.property)
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    have hz : d.action l w - w = 0 := congrArg Subtype.val hw
    obtain ⟨r, x, hx⟩ := (mem_upper_iff_point d s (w : W)).mp
      (seed_le_upper d s mark actors w.property)
    have hx0 : x = 0 := by
      rw [← hx, cubic_displacement d s l a ha he] at hz
      have hproj := congrArg d.projection hz
      rw [cover_projection, point_projection, map_zero] at hproj
      have heq : (a - 1) * x = 0 := congrFun hproj 0
      exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr ha1)
    apply Subtype.ext
    apply Submodule.disjoint_def.mp (seed_disjoint_kernel d sep) _ w.property
    change d.projection w = 0
    rw [← hx, cover_projection, point_projection, hx0]
    funext i
    fin_cases i <;> rfl
  have hs := LinearMap.surjective_of_injective hi
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact (f w).property
  · intro w hw
    obtain ⟨v, hv⟩ := hs ⟨w, hw⟩
    exact ⟨v, congrArg Subtype.val hv⟩

/-- V/V₁ is the marked coordinate line because of its actual cubic L₁ action. -/
theorem seed_eq_marked (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) :
    tilde d V = ((cover d s).toLinearMap.comp markedPointMap).range := by
  let := finite_original d
  obtain ⟨l, hl, a, ha, ha1, he⟩ := actors.cubic
  have hgen := cubic_seed_range d s mark sep actors l hl a ha ha1 he
  have hle : tilde d V ≤ ((cover d s).toLinearMap.comp markedPointMap).range := by
    intro w hw
    obtain ⟨v, hv⟩ := hgen.symm ▸ hw
    obtain ⟨r, x, hx⟩ := (mem_upper_iff_point d s (v : W)).mp
      (seed_le_upper d s mark actors v.property)
    refine ⟨(a - 1) * x, ?_⟩
    change cover d s (point 0 ((a - 1) * x)) = w
    rw [← cubic_displacement d s l a ha he, hx]
    exact hv
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [seed_tilde_finrank d, markedPointMap_finrank (cover d s).toLinearMap
    d.projection.toLinearMap (cover_projection d s)]

/-- The earlier 14.7.65 fixed-space equality with the original seed and projection. -/
theorem upper_eq_seed_sup_kernel (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) :
    SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker := by
  let p := restrictedProjection d.naturalQuotient s.projection
  apply SL2CentralExtension.upperFixed_decomposition _ p.toLinearMap d.projection_onto
    (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v)
    (fun v hv g => s.kernel_fixed hv g) (tilde d V)
    (seed_le_upper d s mark actors)
  · rw [seed_tilde_finrank d]
    exact (SL2NaturalH1.field_finrank 2
      (by rw [Nat.card_eq_fintype_card, card_field]; rfl)).symm
  · exact seed_disjoint_kernel d sep

/-- Every vector in a single displacement has its literal universal-cover coordinates. -/
theorem mem_displacement_iff (h : F.H) (t : SL2FourNatural.F)
    (he : d.qH h = alternatingActor d.naturalQuotient (upper t)) (w : W) :
    w ∈ (d.action h - LinearMap.id).range ↔
      ∃ y : SL2FourNatural.F, cover d s (point (t ^ 2 * y) (t * y)) = w := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨u, rfl⟩ := cover_onto d s v
    refine ⟨(coordinates u).2 1, ?_⟩
    change _ = d.action h (cover d s u) - cover d s u
    rw [actor_cover d s h (upper t) he, ← map_sub, displacement_point]
  · rintro ⟨y, rfl⟩
    refine ⟨cover d s (coordinates.symm (0, ![0, y])), ?_⟩
    change d.action h _ - _ = _
    rw [LinearMap.id_apply, actor_cover d s h (upper t) he, ← map_sub, ← point_is_displacement]

/-- A nonzero displacement line and the cubic-marked line span the full upper space. -/
theorem displacement_sup_seed (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (he : d.qH h = alternatingActor d.naturalQuotient (upper t)) :
    (d.action h - LinearMap.id).range ⊔ tilde d V =
      SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) := by
  apply le_antisymm
  · apply sup_le
    · intro w hw
      obtain ⟨y, rfl⟩ := (mem_displacement_iff d s h t he w).mp hw
      exact (mem_upper_iff_point d s _).mpr ⟨_, _, rfl⟩
    · exact seed_le_upper d s mark actors
  · intro w hw
    obtain ⟨r, x, rfl⟩ := (mem_upper_iff_point d s w).mp hw
    let y := r / t ^ 2
    apply Submodule.mem_sup.mpr
    refine ⟨cover d s (point (t ^ 2 * y) (t * y)),
      (mem_displacement_iff d s h t he _).mpr ⟨y, rfl⟩,
      cover d s (point 0 (x - t * y)), ?_, ?_⟩
    · rw [seed_eq_marked d s mark sep actors]
      exact ⟨x - t * y, rfl⟩
    · rw [← map_add, point_add, add_zero, add_sub_cancel]
      congr 2
      exact mul_div_cancel₀ r (pow_ne_zero 2 ht)

/-- Rank three forces this same cover map to be injective, by actual dimensions. -/
theorem cover_injective (hrank : primeRank 2 d.U₀ = 3) :
    Function.Injective (cover d s) := by
  let := finite_original d
  let := d.U₀_elementary
  have hk := s.kernel_finrank_le_two
  have hn : Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2 := by
    by_contra hne
    have hk1 : Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 1 := by omega
    have hc : Nat.card d.U₀ ≤ 2 ^ 2 := by
      rw [d.U₀_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk1
      omega
    have hr := IsElementaryAbelian.primeRank_le_of_card_le d.U₀ hc
    omega
  have hd := d.projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr d.projection_onto, finrank_top, finrank_vector, hn] at hd
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (cover d s).toLinearMap) _).mpr (cover_onto d s)
  rw [binary_finrank, ← hd]

include s in
/-- The two marked lines meet trivially before any nontrivial central quotient. -/
theorem displacement_disjoint_seed (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hrank : primeRank 2 d.U₀ = 3)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (he : d.qH h = alternatingActor d.naturalQuotient (upper t)) :
    Disjoint (d.action h - LinearMap.id).range (tilde d V) := by
  apply Submodule.disjoint_def.mpr
  intro w hw hv
  obtain ⟨y, hy⟩ := (mem_displacement_iff d s h t he w).mp hw
  rw [seed_eq_marked d s mark sep actors] at hv
  obtain ⟨x, hx⟩ := hv
  change cover d s (point 0 x) = w at hx
  have hp := (point_eq_iff _ _ _ _).mp (cover_injective d s hrank (hy.trans hx.symm))
  have hy0 : y = 0 := (mul_eq_zero.mp hp.1).resolve_left (pow_ne_zero _ ht)
  rw [hy0, mul_zero, mul_zero, point_zero, map_zero] at hy
  exact hy.symm

/-- The spanning calculation in 14.7.70, for any qualifying critical path. -/
theorem commutator_spans (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (h69 : Nat.card (star F c.Uα) = 2) :
    tilde d (Fcomm c) ⊔ tilde d V =
      SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) := by
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  rw [commutator_image d c earlier s h69 h hh (upper_actor_ne_one d h t ht he)]
  exact displacement_sup_seed d s mark sep actors h t ht he

include s in
/-- The rank-three disjointness calculation in 14.7.70, on the very same section. -/
theorem commutator_disjoint (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (h69 : Nat.card (star F c.Uα) = 2)
    (hrank : primeRank 2 d.U₀ = 3) :
    Disjoint (tilde d (Fcomm c)) (tilde d V) := by
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  rw [commutator_image d c earlier s h69 h hh (upper_actor_ne_one d h t ht he)]
  exact displacement_disjoint_seed d s mark sep actors hrank h t ht he

omit s in
/-- The marked calculations discharge both ambient product premises in (*).
Descent is constructed from the literal earlier 14.5.15(4) core action. -/
theorem commutator_products (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : LocalActors d)
    (h69 : Nat.card (star F c.Uα) = 2) :
    Fcomm c ⊔ V = d.U₀ ⊔ V ∧ Fcomm c ⊔ d.U₀ = d.U₀ ⊔ V := by
  let s := d.actionDescentOfCore hcore
  have h65 := upper_eq_seed_sup_kernel d s mark sep actors
  have hspan := commutator_spans d s c earlier mark sep actors h69
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  exact ⟨commutator_sup_seed d c earlier s h65 hspan,
    commutator_sup_U₀ d c earlier s h t ht he
      (commutator_image d c earlier s h69 h hh (upper_actor_ne_one d h t ht he)) h65⟩

omit s in
/-- Application to the rank-three branch with the literal 14.7.68 fusion input.
The point exclusion follows from the proved marked disjointness, not a premise.
Earlier 14.7.39/F.9 and the permitted rechoice's centrality remain with their owners. -/
theorem rank_three_geometry (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : LocalActors d)
    (hrank : primeRank 2 d.U₀ = 3)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hcentral : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G))) :
    Fcomm c ≤ F.U ⊓ c.Uα ∧ c.Zα ≤ Fcomm c ∧ F.Vi 1 ≤ Fcomm c ∧
      (T : Subgroup G) ≤ normalizer (Fcomm c : Set G) ∧
      Nat.card (Fcomm c) = 8 ∧ Fcomm c ⊓ d.U₀ = F.Vi 1 ∧
      ¬ c.Zα ≤ d.U₀ ∧ ¬ c.Zα ≤ V := by
  let s := d.actionDescentOfCore hcore
  obtain ⟨hF, hZ, hP, hn, hc, hi⟩ := preliminary_geometry d c earlier s mark
    selection h69 hUH heven hF9 hF9α hcentral
  have hZ₀ := point_not_le_U₀ d c h69 h68
  have hd := commutator_disjoint d s c earlier mark sep actors h69 hrank
  exact ⟨hF, hZ, hP, hn, hc, hi, hZ₀, point_not_le_seed d c earlier hZ hZ₀ hd⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
