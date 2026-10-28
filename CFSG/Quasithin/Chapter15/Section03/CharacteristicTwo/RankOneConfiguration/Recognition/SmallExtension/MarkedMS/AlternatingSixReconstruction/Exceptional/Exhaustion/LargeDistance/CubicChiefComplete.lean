module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRestrictedActor

/-!
# The unique noncentral radius factor with the cubic kernel retained

The controlled reverse even actor bounds the noncentral chief count of the
literal radius quotient by one. It cannot be zero: residual movement confined
to the seed would identify the radius with its incident edge radius, contrary
to the characteristic condition. Refining through any normal subgroup gives
the source residual dichotomy. Nilpotent saturation excludes its covering
alternative for [V,Q], proving [[V,Q],L] <= Z in the large-image case.

The budget uses the actual two-core and allows simple factors detecting E/Q.
The quotient, component and graph embeddings are unchanged. The final
whole-core and literal rank-two applications discharge all Section 5.2
radius premises; terminal path exclusions and both reconstruction outcomes
remain with qt-e-ms-small-a6-reconstruction.
Source: MS93 (5.2)(i), p.914, and (5.12)(2), pp.925--926. The proof adapts
Natural.Exhaustion.LargeDistance.SectionFive.ChiefFactor.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
/-- The full radius in the original vertex group, through `embedM`. -/
abbrev radiusPreimage (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  (V (edge L R) (alpha (edge L R))).comap (embedM (edge L R))

/-- The full initial Z-seed in the same vertex group. -/
abbrev radiusSeed (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  (Z (edge L R) (alpha (edge L R))).comap (embedM (edge L R))

instance radiusPreimage_normal (L R : Subgroup G) : (radiusPreimage L R).Normal :=
  radius_comap_normal (L := L) (R := R)

instance radiusSeed_normal (L R : Subgroup G) : (radiusSeed L R).Normal :=
  CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSeed.Z_comap_normal (edge L R)

/-- The actual radius image in the quotient by the full Z-seed. -/
def radiusQuotient (L R : Subgroup G) : Subgroup ((L ⊔ R : Subgroup G) ⧸ radiusSeed L R) :=
  (radiusPreimage L R).map (QuotientGroup.mk' (radiusSeed L R))

instance radiusQuotient_normal (L R : Subgroup G) : (radiusQuotient L R).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem radiusSeed_le_radiusPreimage : radiusSeed L R ≤ radiusPreimage L R :=
  comap_mono (Z_le_VBall T (alpha T) 2)

omit [Finite G] in
private theorem radiusSeed_le_edge_preimage :
    radiusSeed L R ≤ (V T (beta T)).comap (embedM T) := by
  apply comap_mono
  apply le_iSup_of_le (alpha T)
  apply le_iSup_of_le (show (cosetGraph T).dist (alpha T)
    (beta T) ≤ 2 from ?_)
  · exact le_rfl
  · exact (SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj T (alpha T) (beta T)).mpr
        (base_adjacent T))).le.trans (by decide)

include h e hz hk in
private theorem radius_not_le_edge_preimage (hb : 2 < sourceDistance h) :
    ¬ radiusPreimage L R ≤ (V T (beta T)).comap (embedM T) := by
  intro hVE
  have hVeq : V T (alpha T) = V T (beta T) := by
    apply le_antisymm _ (edge_radius_le_radius rfl (base_adjacent T))
    have hh := map_mono (f := embedM T) hVE
    rwa [radius_comap_map (h := h) hb,edge_radius_comap_map (h := h) hb] at hh
  have hVQ : V T (alpha T) ≤ Q T (alpha T) :=
    V_le_Q T rfl hb
  have hbot := no_common_normal_at_edge T h.relative_characteristic
    (alpha T) (beta T) rfl (base_adjacent T)
    (V T (alpha T))
    (le_inf (hVQ.trans (fun _ hx => hx.1))
      (hVQ.trans (fun _ hx => hx.2 _ (base_adjacent T))))
    (normal_subgroupOf_of_le_normalizer (V_normalized (alpha T)))
    (by rw [hVeq]; exact normal_subgroupOf_of_le_normalizer (V_normalized (beta T)))
  have hU : U T (alpha T) = ⊥ := le_bot_iff.mp
    (((DistanceEight.U_le_Z T _).trans (Z_le_VBall T _ 2)).trans hbot.le)
  have hcard := graph_U_card h e hz hk (alpha T) rfl
  rw [hU,card_bot] at hcard
  omega

include h e hz hk in
/-- Residual movement of the full radius cannot be confined to the initial seed. -/
theorem radius_moving_not_le_seed (hb : 2 < sourceDistance h) :
    ¬ ⁅radiusPreimage L R,(L.subgroupOf (L ⊔ R))⁆ ≤ radiusSeed L R := by
  intro hsmall
  apply radius_not_le_edge_preimage h e hz hk hb
  exact (radius_comap_le_edge_sup_commutator (h := h) hb).trans
    (sup_le le_rfl (hsmall.trans (radiusSeed_le_edge_preimage (L := L) (R := R))))


include h e hz hk in
/-- The literal radius quotient has nontrivial two-residual action. -/
theorem radiusQuotient_moving_ne_bot (hb : 2 < sourceDistance h) :
    ⁅radiusQuotient L R,pResidual 2 (M ⧸ radiusSeed L R)⁆ ≠ ⊥ := by
  intro hzq
  apply radius_moving_not_le_seed h e hz hk hb
  let π := QuotientGroup.mk' (radiusSeed L R)
  have hm : (⁅radiusPreimage L R,(L.subgroupOf (L ⊔ R))⁆).map π = ⊥ := by
    rw [map_commutator,show (L.subgroupOf (L ⊔ R)) = pResidual 2 M from h.relative_residual.symm,map_pResidual_quotient]
    exact hzq
  have hh := (Subgroup.map_eq_bot_iff _).mp hm
  simpa only [π,QuotientGroup.ker_mk'] using hh

include h e hz hk in
/-- MS93 (5.2)(i) with the cubic kernel retained: every chief series of the actual radius
quotient has exactly one noncentral factor under the source critical-index hypothesis. -/
theorem critical_radius_unique_noncentral_factor
    (hb : 2 < sourceDistance h)
    {a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T (alpha T)))
    (c : SeriesOn (radiusQuotient L R)) : c.noncentralCount = 1 := by
  obtain ⟨W,hWU,hcomm,a,haW,ha,heven⟩ := critical_radius_even_actor h e hz hk p hforward
  let f := embedM T
  let A := W.comap f
  let K := (Q T (p.walk.getVert (p.walk.length-2))).comap f
  let π := QuotientGroup.mk' (radiusSeed L R)
  have hV : radiusPreimage L R ≤ pCore 2 M := by
    have hh := comap_mono (f := f) (V_le_Q T
      (geometry := sourceGeometry h) (a := alpha T) rfl hb)
    rwa [Q_alpha_comap T h.relative_radical.isPGroup
      h.relative_radical.twoCore_le] at hh
  have hWrange : W ≤ f.range := by
    change W ≤ Mbar T
    rw [←stabilizer_m_base]
    exact (hWU.trans (DistanceEight.U_le_Z T a')).trans
      (critical_Z_le_stabilizer T (sourceGeometry h) (alpha T) rfl
        (sourceDistance_pos h) p.critical)
  have hWmap : A.map f = W := map_comap_eq_self hWrange
  have hcomm₀ : ⁅radiusPreimage L R ⊓ K,A⁆ ≤ radiusSeed L R := by
    apply (map_le_map_iff_of_injective (embedM_injective T)).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective T),
      radius_comap_map (h := h) hb,hWmap]
    exact ((commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans
      hcomm).trans (map_comap_eq_self ((Z_le_stabilizer T _).trans_eq
        (stabilizer_m_base T))).ge
  have hindex : K.relIndex (radiusPreimage L R) ≤ 8 := by
    rw [relIndex_comap,radius_comap_map (h := h) hb]
    exact critical_radius_image_index_le_eight h e hz hk p
  have hfixed := (SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
    (radiusPreimage L R) A (radiusSeed L R) K hcomm₀).trans hindex
  have hfixedq : (centralizer (A.map π : Set (M ⧸ radiusSeed L R))).relIndex
      (radiusQuotient L R) ≤ 8 := by
    rwa [SymmetricSixBudget.centralizerModulo_relIndex_eq] at hfixed
  have htwo : IsPGroup 2 (radiusQuotient L R) :=
    (pCore_isPGroup.to_le hV).map π
  have hcount := quotient_noncentralCount_le_one h e hz hk π (QuotientGroup.mk'_surjective _)
    (radiusQuotient L R) htwo A a ha heven haW hfixedq c
  have hpos : c.noncentralCount ≠ 0 := by
    intro hzero
    have hh := c.series.residual_commutator_le_head_of_central_steps
      (show IsPGroup 2 c.series.last.val by rw [c.last_eq]; exact htwo)
      (c.noncentralCount_eq_zero_iff.mp hzero)
    rw [c.last_eq,c.head_eq] at hh
    exact radiusQuotient_moving_ne_bot h e hz hk hb (le_bot_iff.mp hh)
  omega

include h e hz hk in
/-- Apply the unique chief factor to an arbitrary subgroup normal in the
original vertex group, retaining the actual commutators and seed. -/
theorem critical_radius_normal_subgroup_dichotomy
    (hb : 2 < sourceDistance h)
    {a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T (alpha T)))
    (Y : Subgroup M) [Y.Normal] (hY : Y ≤ radiusPreimage L R) :
    ⁅Y,(L.subgroupOf (L ⊔ R))⁆ ≤ radiusSeed L R ∨
      ⁅radiusPreimage L R,(L.subgroupOf (L ⊔ R))⁆ ≤ Y ⊔ radiusSeed L R := by
  let π := QuotientGroup.mk' (radiusSeed L R)
  let : (Y.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  obtain ⟨c⟩ := SeriesOn.exists_series (radiusQuotient L R)
  have hc1 := critical_radius_unique_noncentral_factor h e hz hk hb p hforward c
  have hV : radiusPreimage L R ≤ pCore 2 M := by
    have hh := comap_mono (f := embedM T) (V_le_Q T
      (geometry := sourceGeometry h) (a := alpha T) rfl hb)
    rwa [Q_alpha_comap T h.relative_radical.isPGroup
      h.relative_radical.twoCore_le] at hh
  have htwo : IsPGroup 2 (radiusQuotient L R) :=
    ((pCore_isPGroup (p := 2) (G := M)).to_le hV).map π
  have hres : ((L.subgroupOf (L ⊔ R))).map π = pResidual 2 (M ⧸ radiusSeed L R) := by
    rw [show (L.subgroupOf (L ⊔ R)) = pResidual 2 M from h.relative_residual.symm,map_pResidual_quotient]
  rcases c.residual_dichotomy_of_count_one htwo hc1 (Y.map π) (map_mono hY) with hfixed | hcover
  · left
    have hh : (⁅Y,(L.subgroupOf (L ⊔ R))⁆).map π = ⊥ := by
      rwa [map_commutator,hres]
    have hk := (Subgroup.map_eq_bot_iff _).mp hh
    simpa only [π,QuotientGroup.ker_mk'] using hk
  · right
    have hh : (⁅radiusPreimage L R,(L.subgroupOf (L ⊔ R))⁆).map π ≤ Y.map π := by
      rwa [map_commutator,hres]
    have hk := (map_le_iff_le_comap).mp hh
    simpa only [comap_map_eq,π,QuotientGroup.ker_mk'] using hk


include h e hz hk in
/-- In the actual source radius the covering alternative for its two-kernel
commutator is impossible: nilpotent saturation would identify the full
radius with its edge radius. -/
theorem critical_radius_kernel_residual_le_seed
    (hb : 2 < sourceDistance h)
    {a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T (alpha T))) :
    ⁅⁅radiusPreimage L R,pCore 2 M⁆,(L.subgroupOf (L ⊔ R))⁆ ≤ radiusSeed L R := by
  rcases critical_radius_normal_subgroup_dichotomy h e hz hk hb p hforward
      ⁅radiusPreimage L R,pCore 2 M⁆ (commutator_le_left _ _) with hfixed | hcover
  · exact hfixed
  · exfalso
    let E := (V T (beta T)).comap (embedM T)
    have hV : radiusPreimage L R ≤ pCore 2 M := by
      have hh := comap_mono (f := embedM T) (V_le_Q T
        (geometry := sourceGeometry h) (a := alpha T) rfl hb)
      rwa [Q_alpha_comap T h.relative_radical.isPGroup
        h.relative_radical.twoCore_le] at hh
    have hEV : E ≤ radiusPreimage L R := comap_mono
      (edge_radius_le_radius rfl (base_adjacent T))
    have hbound : radiusPreimage L R ≤ E ⊔ ⁅radiusPreimage L R,pCore 2 M⁆ := by
      apply (radius_comap_le_edge_sup_commutator (h := h) hb).trans
      apply sup_le le_sup_left
      exact hcover.trans (sup_le le_sup_right ((radiusSeed_le_edge_preimage (L := L) (R := R)).trans le_sup_left))
    have hVE : radiusPreimage L R ≤ E :=
      le_of_le_sup_commutator_of_isNilpotent (pCore 2 M) (radiusPreimage L R) E
        (pCore 2 M) (pCore_isPGroup (p := 2) (G := M)).isNilpotent
        hV (hEV.trans hV) le_rfl
        (h.relative_radical.twoCore_le.trans (radical_normalizes_edge_radius_comap (L := L) (R := R))) hbound
    exact radius_not_le_edge_preimage h e hz hk hb hVE

include h e hz hk in
/-- The strengthened large-image conclusion on the literal graph radius,
with the original component and kernel embeddings. -/
theorem critical_radius_kernel_residual_le_Z
    (hb : 2 < sourceDistance h)
    {a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T (alpha T))) :
    ⁅⁅V T (alpha T),Q T (alpha T)⁆,
      Ltilde T (alpha T)⁆ ≤ Z T (alpha T) := by
  have hh := map_mono (f := embedM T)
    (critical_radius_kernel_residual_le_seed h e hz hk hb p hforward)
  have hL : ((L.subgroupOf (L ⊔ R))).map (embedM T) = Ltilde T (alpha T) := by
    rw [Ltilde_alpha]
    exact congrArg (Subgroup.map (embedM T)) h.relative_residual.symm
  have hZ : (radiusSeed L R).map (embedM T) = Z T (alpha T) :=
    map_comap_eq_self ((Z_le_stabilizer T _).trans_eq (stabilizer_m_base T))
  rwa [map_commutator,map_commutator,radius_comap_map (h := h) hb,
    ←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,hL,hZ] at hh


omit hk in
include h e hz in
/-- The complete Section 5.2 radius family in the only remaining cubic
whole-core branch. The terminal path exclusions are still required. -/
theorem coreExhaustion_or_cubic_sectionFive :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex T, color T a = false → ∀ a' c : Vertex T,
        ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
        ⁅V T a,V T a⁆ ≤ X T a ∧
        ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥) ∧
      ∀ c : Vertex T, ∀ _p : CriticalPath T (sourceGeometry h) (alpha T) c,
        4 ≤ (Q T c).relIndex (Z T (alpha T)) →
        (∀ s : SeriesOn (radiusQuotient L R), s.noncentralCount = 1) ∧
        ⁅⁅V T (alpha T),Q T (alpha T)⁆,Ltilde T (alpha T)⁆ ≤ Z T (alpha T) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,radius_bounds_at h e hz hk,
      fun _ p hf => ⟨critical_radius_unique_noncentral_factor h e hz hk hb p hf,
        critical_radius_kernel_residual_le_Z h e hz hk hb p hf⟩⟩

omit hk in
include h e hz in
/-- The literal rank-two consumer, with every Section 5.2 actor, centrality
and chief-factor premise discharged on the original graph. -/
theorem rankTwo_or_cubic_sectionFive :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex T, color T a = false → ∀ a' c : Vertex T,
        ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
        ⁅V T a,V T a⁆ ≤ X T a ∧
        ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥) ∧
      ∀ c : Vertex T, ∀ _p : CriticalPath T (sourceGeometry h) (alpha T) c,
        4 ≤ (Q T c).relIndex (Z T (alpha T)) →
        (∀ s : SeriesOn (radiusQuotient L R), s.noncentralCount = 1) ∧
        ⁅⁅V T (alpha T),Q T (alpha T)⁆,Ltilde T (alpha T)⁆ ≤ Z T (alpha T) :=
  (coreExhaustion_or_cubic_sectionFive h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
