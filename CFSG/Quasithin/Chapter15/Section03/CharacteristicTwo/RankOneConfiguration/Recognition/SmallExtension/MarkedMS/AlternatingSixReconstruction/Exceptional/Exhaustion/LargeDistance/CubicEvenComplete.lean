module
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.GroupTheory.PCoreActionSplitting
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEven

/-!
# Exclusion of the cubic even-image branch

The even initial natural image implies that the whole vertex quotient by
Q is the original triple cover. Its projection therefore has kernel Q,
although the initial natural action still has the larger cubic kernel E.
All radius inverse images retain E. A two-subgroup meets E in Q because
E/Q has order three; this gives the midpoint index bound four and the
moving central quotient's fixed codimension bound two.

The actual initial moved quotient gives at least four commutators for
an escaping even involution. This lower bound survives in the radius and
its moving subgroup. Full residual movement and zero fixed space let the
small-involution theorem recognize the moving central quotient as either
the natural four-space or the hexacode. Their derived-order and invariant-form
bounds contradict the lower bound. Thus the even image is impossible.

The entire-core and literal rank-two applications now retain only the
cubic full-symmetric action at larger distance. Its Section 5 exhaustion,
and the final natural/exceptional assembly, remain with
qt-e-ms-small-a6-reconstruction. No kernel, central attachment, or original
action is replaced, and the radical is not assumed to be Sylow.

Source: Meierfrankenfeld--Stellmacher (1993), (3.8), pp.877--879;
Aschbacher--Smith C.1.31--32, pp.135--136. The concrete hexacode results
retain the attribution and license documented in their imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEven
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "ρ" => BinaryPermutation.naturalRepresentation (Fin 6)

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "π" => CubicAction.projection h e hz hk
local notation "K" => L.subgroupOf (L ⊔ R)

include h e hz hk
/-- The even natural image leaves no outer factor above the actual component. -/
theorem component_sup_core_eq_top
    (himage : (π).range = alternatingGroup (Fin 6)) : K ⊔ pCore 2 M = ⊤ := by
  have he : extensionKernel h ≤ K ⊔ pCore 2 M :=
    sup_le (map_subtype_le _ |>.trans le_sup_left) le_sup_right
  have hm : (K).map π = (π).range := (CubicAction.component_image h e hz hk).trans himage.symm
  have hh := congrArg (fun A : Subgroup (Equiv.Perm (Fin 6)) => A.comap π) hm
  have hr : (π).range.comap π = ⊤ := top_unique (fun x _ => ⟨x,rfl⟩)
  rw [comap_map_eq,hr,CubicAction.projection_kernel] at hh
  exact top_unique (hh.symm.trans_le (sup_le le_sup_left he))

/-- The full quotient by Q is the component's triple cover, not the initial natural actor. -/
theorem quotient_hexEven
    (himage : (π).range = alternatingGroup (Fin 6)) :
    Nonempty ((M ⧸ pCore 2 M) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  have hC : componentImage L R = ⊤ := by
    have hm := congrArg (fun A : Subgroup M => A.map (QuotientGroup.mk' (pCore 2 M)))
      (component_sup_core_eq_top h e hz hk himage)
    simpa only [Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] using hm
  obtain ⟨a,_⟩ := exists_quotient_hexacode_equiv h e hz
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let c := (cComponentTwoCoreQuotientEquiv h.component).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans a)
  exact ⟨((MulEquiv.subgroupCongr hC).trans topEquiv).symm.trans c⟩

namespace Chart
variable {a : Vertex (edge L R)} (c : Chart (L := L) (R := R) a)

omit e hz hk in
/-- The chart carries the intrinsic two-core to the literal neighborhood kernel. -/
theorem map_Q (ha : color T a = false) : (pCore 2 M).map c.embedding = Q T a := by
  rw [←pCoreIn_range_of_injective 2 c.embedding c.injective,c.range_eq]
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)
  have hf := (MulAut.conj g⁻¹).injective.comp (embedM_injective T)
  have hr : f.range = stabilizer T (mVertex T g) := by
    rw [MonoidHom.range_comp]
    change (Mbar T).map _ = _
    rw [←stabilizer_m_base T]
    simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act T g (alpha T)).symm
  have hq : (pCore 2 M).map f = Q T (mVertex T g) := by
    rw [←map_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    simpa only [alpha,act_mVertex,one_mul] using (Q_act T g (alpha T)).symm
  rwa [←pCoreIn_range_of_injective 2 f hf,hr] at hq

omit e hk in
/-- A two-subgroup meets the retained E-kernel exactly in Q. -/
theorem inf_kernel_eq_inf_Q (ha : color T a = false) (A : Subgroup (FreeAmalgam T))
    (hA : IsPGroup 2 A) : A ⊓ c.kernel h = A ⊓ Q T a := by
  have hCQ : (c.kernel h).comap c.embedding = extensionKernel h := by
    rw [kernel,comap_map_eq_self_of_injective c.injective]
  have hm : ((A ⊓ c.kernel h).comap c.embedding).map c.embedding = A ⊓ c.kernel h :=
    map_comap_eq_self (inf_le_right.trans (map_le_range _ _))
  have ht : IsPGroup 2 ((A ⊓ c.kernel h).comap c.embedding) :=
    (hA.of_injective (inclusion inf_le_left) (inclusion_injective _)).of_injective
      (c.embedding.subgroupComap _) (fun _ _ hh => Subtype.ext (c.injective (congrArg Subtype.val hh)))
  have hl := two_subgroup_le_core_of_le_extensionKernel h hz _ ht
    ((comap_mono inf_le_right).trans_eq hCQ)
  have hAQ : A ⊓ c.kernel h ≤ Q T a := by
    rw [←hm,←c.map_Q h ha]
    exact map_mono hl
  exact le_antisymm (le_inf inf_le_left hAQ)
    (inf_le_inf_left _ (by rw [←c.map_Q h ha]; exact map_mono le_sup_right))

omit e hk in
/-- The odd quotient E/Q changes no displacement index of a two-subgroup. -/
theorem kernel_index_eq (ha : color T a = false) (A : Subgroup (FreeAmalgam T)) (hA : IsPGroup 2 A) :
    (c.kernel h).relIndex A = (Q T a).relIndex A := by
  rw [←inf_relIndex_left A (c.kernel h),c.inf_kernel_eq_inf_Q h hz ha A hA,
    inf_relIndex_left]
end Chart

private theorem radius_le_critical_join
    (himage : (π).range = alternatingGroup (Fin 6))
    (a c : Vertex T) (ha : color T a = false) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2)
    (t : Vertex T) (hat : Adjacent T a t) (hct : Adjacent T c t)
    (d : Vertex T) (hcd : CriticalPair T c d ((sourceGeometry h).exists_critical c hcColor))
    (htd : (cosetGraph T).dist t d + 1 = (cosetGraph T).dist c d)
    (z : Chart (L := L) (R := R) c) :
    V T a ≤ X T d ⊔ z.kernel h := by
  have hfour := distance_eq_four h e hz hk himage
  have hta : (cosetGraph T).dist t a = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr (adjacent_symm T hat))
  have hct1 : (cosetGraph T).dist c t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hct)
  apply NaturalStructure.Exclusion.radius_le_of_m_ball ha
  intro f hf hfa
  by_cases hfQ : Z T f ≤ Q T c
  · have hQE : Q T c ≤ z.kernel h := by
      rw [←z.map_Q h hcColor]; exact map_mono le_sup_right
    exact hfQ.trans (hQE.trans le_sup_right)
  have hmin := criticalDistance_le T f ((sourceGeometry h).exists_critical f hf) hfQ
  have hfcrit : criticalDistance T f ((sourceGeometry h).exists_critical f hf) = 4 :=
    ((sourceGeometry h).distance_constant f hf).trans hfour
  rw [hfcrit] at hmin
  have htri := (cosetGraph_connected T).dist_triangle (u := f) (v := a) (w := c)
  have hfc : (cosetGraph T).dist f c = 4 := by omega
  have hpair : CriticalPair T f c ((sourceGeometry h).exists_critical f hf) :=
    ⟨hfc.trans hfcrit.symm,hfQ⟩
  have hrev := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    f hf (by rw [(sourceGeometry h).distance_constant f hf]; exact sourceDistance_pos h)
    c hcColor hpair
  have htf : (cosetGraph T).dist t f + 1 = (cosetGraph T).dist c f := by
    have h₁ := (cosetGraph_connected T).dist_triangle (u := t) (v := a) (w := f)
    have h₂ := (cosetGraph_connected T).dist_triangle (u := c) (v := t) (w := f)
    have haf : (cosetGraph T).dist a f ≤ 2 := by simpa only [SimpleGraph.dist_comm] using hfa
    have hcf : (cosetGraph T).dist c f = 4 := by rwa [SimpleGraph.dist_comm]
    omega
  have hj := z.critical_join_common h e hz hk himage hcColor d hcd t hct htd f hrev htf
  have hZX := (sourceGeometry h).omega_bound f hf (by rw [hfcrit]; decide)
  exact hZX.trans (le_sup_left.trans hj.ge)

omit h e hz hk [Finite G] in
private theorem relIndex_join_of_normalizes {H : Type*} [Group H]
    (E N : Subgroup H) (hEN : E ≤ normalizer (N : Set H)) :
    N.relIndex (E ⊔ N) = N.relIndex E := by
  let := normal_subgroupOf_of_le_normalizer hEN
  let := normal_subgroupOf_sup_of_le_normalizer hEN
  exact Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hEN).toEquiv.symm

/-- The radius image modulo the actual midpoint kernel has order at most four. -/
theorem radius_index_le_four
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcb : (cosetGraph T).dist c b = 2) :
    (Q T c).relIndex (V T a) ≤ 4 := by
  have hd : (cosetGraph T).dist a b = 4 :=
    (hc.1.trans ((sourceGeometry h).distance_constant a ha)).trans
      (distance_eq_four h e hz hk himage)
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two T a c hac
  have htb : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj T _ _).mpr (adjacent_symm T hct))
    have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := b)
    have h₂ := (cosetGraph_connected T).dist_triangle (u := t) (v := c) (w := b)
    omega
  obtain ⟨g,hgt,hga⟩ := stabilizer_transitive_neighbors T t
    (adjacent_symm T hat) (adjacent_symm T hct)
  have hgt' : act T g t = t := hgt
  have hcol : color T (act T g a) = false := by rw [hga]; exact hcColor
  have hcg : CriticalPair T c (act T g b) ((sourceGeometry h).exists_critical c hcColor) := by
    simpa only [hga] using (criticalPair_act_iff T g a b ((sourceGeometry h).exists_critical a ha)
      ((sourceGeometry h).exists_critical (act T g a) hcol)).mpr hc
  have htg : (cosetGraph T).dist t (act T g b) + 1 =
      (cosetGraph T).dist c (act T g b) := by
    rw [←hgt',←hga,dist_act,dist_act]
    exact htb
  obtain ⟨z⟩ := chart_nonempty h c hcColor
  have hV := radius_le_critical_join h e hz hk himage a c ha hcColor hac
    t hat hct (act T g b) hcg htg z
  have hgcol := critical_endpoint_color T c hcColor _ hcg
  have hrev := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    c hcColor (by rw [(sourceGeometry h).distance_constant c hcColor]; exact sourceDistance_pos h)
    _ hgcol hcg
  have hX := critical_X_le_vertex h e _ hgcol _ hrev
  have hJ : X T (act T g b) ⊔ z.kernel h ≤ stabilizer T c := sup_le hX ((map_le_range _ _).trans_eq z.range_eq)
  let := finite_stabilizer T c
  let : Finite (X T (act T g b) ⊔ z.kernel h : Subgroup (FreeAmalgam T)) :=
    Finite.of_injective (inclusion hJ) (inclusion_injective hJ)
  have hpV : IsPGroup 2 (V T a) :=
    (Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le a ha).of_injective
      (inclusion ((sourceGeometry h).V_le_Q (by change 2 < sourceDistance h; rw [distance_eq_four h e hz hk himage]; decide) a ha))
      (inclusion_injective _)
  have hnE : stabilizer T c ≤ normalizer (z.kernel h : Set (FreeAmalgam T)) := by
    have hh := le_normalizer_map z.embedding (H := extensionKernel h)
    rw [normalizer_eq_top_iff.mpr (inferInstance : (extensionKernel h).Normal),
      ←MonoidHom.range_eq_map,z.range_eq] at hh
    exact hh
  rw [←z.kernel_index_eq h hz hcColor _ hpV]
  calc
    (z.kernel h).relIndex (V T a) ≤ (z.kernel h).relIndex (X T (act T g b) ⊔ z.kernel h) :=
      relIndex_le_of_le_right hV
        ((z.kernel h).subgroupOf (X T (act T g b) ⊔ z.kernel h)).index_ne_zero_of_finite
    _ = (z.kernel h).relIndex (X T (act T g b)) :=
      relIndex_join_of_normalizes _ _ (hX.trans hnE)
    _ = 4 := by
      let : IsElementaryAbelian 2 (X T (act T g b)) := omegaCenter_elementary _
      rw [z.kernel_index_eq h hz hcColor _ (IsElementaryAbelian.isPGroup 2 _)]
      exact (critical_indices h e hz hk himage c hcColor _ hcg).1


/-- The full-X source estimate at a critical midpoint. -/
theorem radius_intersection_X
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hcb : (cosetGraph T).dist c b = 2) :
    ⁅V T a ⊓ Q T c,X T b⁆ ≤ ⁅X T a,X T b⁆ := by
  have hb : 2 < sourceDistance h := by rw [distance_eq_four h e hz hk himage]; decide
  exact critical_actor_bound h e hz hk himage a ha b hc _
    (inf_le_right.trans (Q_le_stabilizer_of_dist_two T c b hcColor hcb))
    (inf_le_left.trans (((sourceGeometry h).V_le_Q hb a ha).trans (Q_le_centralizer_X T a)))

/-- The literal moving central quotient has the source displacement budget two. -/
theorem moving_fixedCodim_le_two
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcb : (cosetGraph T).dist c b = 2) :
    letI := NaturalStructure.Exclusion.moving_central_quotient_elementary
      (sourceGeometry h) (sourceDistance_pos h) a ha (radius_derived_le_fixed h e hz hk himage a ha)
    fixedCodim (Offenders.linearize (NaturalStructure.Exclusion.movingQuotientAction a))
      ((X T b).subgroupOf (stabilizer T a)) ≤ 2 := by
  let := NaturalStructure.Exclusion.moving_central_quotient_elementary
    (sourceGeometry h) (sourceDistance_pos h) a ha (radius_derived_le_fixed h e hz hk himage a ha)
  have hb : 2 < sourceDistance h := by rw [distance_eq_four h e hz hk himage]; decide
  have hi := moving_fixedCodim_pow_le_radius_index_X (sourceGeometry h) hb a ha
    (radius_derived_le_fixed h e hz hk himage a ha) (X T b) (Q T c)
    ((radius_intersection_X h e hz hk himage a ha b hc c hcColor hcb).trans
      ((critical_X_commutator_le h e a ha b hc).trans inf_le_left))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hi.trans (radius_index_le_four h e hz hk himage a ha b hc c hcColor hac hcb))

/-- The actual stabilizer has a surjective triple-cover projection with kernel Q. -/
theorem cover_projection
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) :
    ∃ f : stabilizer T a →* Atlas.Codes.HexAutomorphisms,
      f.ker = (Q T a).subgroupOf (stabilizer T a) ∧
      f.range = Atlas.Codes.hexSign.ker := by
  obtain ⟨c⟩ := chart_nonempty h a ha
  obtain ⟨d⟩ := quotient_hexEven h e hz hk himage
  let b : M ≃* stabilizer T a := (MonoidHom.ofInjective c.injective).trans
    (MulEquiv.subgroupCongr c.range_eq)
  have hbval (x : M) : (b x).val = c.embedding x := rfl
  have hQc : (Q T a).comap c.embedding = pCore 2 M := by
    rw [←c.map_Q h ha,comap_map_eq_self_of_injective c.injective]
  let f := Atlas.Codes.hexSign.ker.subtype.comp
    (d.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 M)).comp b.symm.toMonoidHom))
  refine ⟨f,?_,?_⟩
  · ext x
    have hv : c.embedding (b.symm x) = x.val := congrArg Subtype.val (b.apply_symm_apply x)
    have he : f x = 1 ↔ QuotientGroup.mk' (pCore 2 M) (b.symm x) = 1 := by
      change (d (QuotientGroup.mk' (pCore 2 M) (b.symm x))).val = 1 ↔ _
      rw [←show (d (1 : M ⧸ pCore 2 M)).val = (1 : Atlas.Codes.HexAutomorphisms) from
        congrArg Subtype.val d.map_one]
      exact (Atlas.Codes.hexSign.ker.subtype_injective.eq_iff).trans d.injective.eq_iff
    change f x = 1 ↔ x.val ∈ Q T a
    rw [he]
    change (QuotientGroup.mk (b.symm x) : M ⧸ pCore 2 M) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff,←hQc]
    change c.embedding (b.symm x) ∈ Q T a ↔ _
    rw [hv]
  · rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (d.surjective.comp
        ((QuotientGroup.mk'_surjective _).comp b.symm.surjective)),
      ←MonoidHom.range_eq_map,range_subtype]

/-- The natural moved quotient bounds displacement on the whole initial moved subgroup. -/
theorem natural_index_le_initialMoved (A : Subgroup M) :
    2 ^ fixedCodim ρ (A.map π) ≤
      (centralizer (A : Set M)).relIndex (initialMoved L R) := by
  let := h.relative_normal
  let := initialMoved_normal h
  let s := layerSection h
  let q := QuotientGroup.mk' (layerKernel L R)
  let E := NormalElementaryQuotient.movedEquiv (centralOmega L R) q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K
  let c := CubicAction.coordinates h e hz hk
  let F := ((s).coverProjection c).toLinearMap.comp E.toLinearMap
  let σ := NormalElementaryQuotient.originalAction (initialMoved L R)
  have hE (g : M) (v : Additive (initialMoved L R)) :
      E (σ g v) = (s).space.toRepresentation (q g) (E v) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.originalAction_apply (initialMoved L R) g v).trans
      (NormalElementaryQuotient.representation_apply (centralOmega L R) q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g (E v).val).symm
  have hF (g : M) (v : Additive (initialMoved L R)) : F (σ g v) = ρ (π g) (F v) := by
    change (s).coverProjection c (E (σ g v)) = _
    rw [hE]
    exact ((s).coverProjection_ambient c (q g) (E v)).trans
      (CubicAction.permutationAction_apply h e hz hk (q g) (F v))
  have hf : Function.Surjective F :=
    ((s).coverProjection_isCover (layer_moved_alternating h e hz hk).1 c).1.comp E.surjective
  have hcod := fixedCodim_le_of_equivariant_surjection σ ((ρ).comp π) F hf hF A
  unfold fixedCodim at hcod
  rw [Representation.BinaryOffender.fixedSpace_comp_map (ρ) π A] at hcod
  change fixedCodim (ρ) (A.map π) ≤ fixedCodim σ A at hcod
  rw [←inf_relIndex_left (initialMoved L R),NormalElementaryQuotient.original_fixed_index]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hcod

/-- Every escaping even involution creates at least four actual initial commutators. -/
theorem initialMoved_commutator_lower
    (himage : (π).range = alternatingGroup (Fin 6))
    (g : M) (hg : g ^ 2 = 1) (hne : g ∉ pCore 2 M) :
    4 ≤ Nat.card (⁅initialMoved L R,zpowers g⁆ : Subgroup M) := by
  have hgn : π g ≠ 1 := by
    intro hzπ
    have hp : IsPGroup 2 (zpowers g) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers,pow_one]
      exact orderOf_dvd_of_pow_eq_one hg)
    have hq := two_subgroup_le_core_of_le_extensionKernel h hz (zpowers g) hp (by
      rw [←CubicAction.projection_kernel h e hz hk]
      exact zpowers_le.mpr hzπ)
    exact hne (hq (mem_zpowers g))
  have hgeven : π g ∈ alternatingGroup (Fin 6) := himage ▸ (show π g ∈ (π).range from ⟨g,rfl⟩)
  let t : alternatingGroup (Fin 6) := ⟨π g,hgeven⟩
  have ht : orderOf t = 2 := orderOf_eq_prime
    (Subtype.ext (by change (π g)^2=1; rw [←map_pow,hg,map_one]))
    (fun he => hgn (congrArg Subtype.val he))
  have hl := Representation.AlternatingSixInvolutionDisplacement.displacement_lower
    ((ρ).comp (alternatingGroup (Fin 6)).subtype)
    ((BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)).comp
      (alternatingGroup (Fin 6)).subtype_injective) t ht
  rw [←fixedCodim_zpowers_eq_displacement_rank] at hl
  unfold fixedCodim at hl
  rw [Representation.BinaryOffender.fixedSpace_comp_map (ρ) (alternatingGroup (Fin 6)).subtype (zpowers t)] at hl
  change 2 ≤ fixedCodim ρ ((zpowers t).map (alternatingGroup (Fin 6)).subtype) at hl
  rw [MonoidHom.map_zpowers] at hl
  have hi := natural_index_le_initialMoved h e hz hk (zpowers g)
  rw [MonoidHom.map_zpowers] at hi
  have hc := centralizer_relIndex_le_card_of_abelian_commutator
    (initialMoved L R) (initialMoved L R) ⁅initialMoved L R,zpowers g⁆ le_rfl g
    (by let := initialMoved_normal h; exact le_normalizer_of_normal (mem_top g))
    (fun x hx => commutator_mem_commutator hx (mem_zpowers g))
  rw [←centralizer_closure,←Subgroup.zpowers_eq_closure] at hc
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl).trans (hi.trans hc)

open NaturalStructure.Exclusion
/-- The critical involution forces four actual commutators in its midpoint radius. -/
theorem midpoint_derived_card_lower (himage : (π).range = alternatingGroup (Fin 6))
    (b : Vertex T)
    (hcrit : CriticalPair T (alpha T) b ((sourceGeometry h).exists_critical (alpha T) rfl))
    (c : Vertex T) (hc : color T c = false)
    (hac : (cosetGraph T).dist (alpha T) c = 2)
    (hcb : (cosetGraph T).dist c b = 2) :
    4 ≤ Nat.card (⁅V T c,V T c⁆ : Subgroup (FreeAmalgam T)) := by
  have hb : 2 < sourceDistance h := by rw [distance_eq_four h e hz hk himage]; decide
  let f := embedM T
  have hbColor := critical_endpoint_color T (alpha T) rfl _ hcrit
  have hreverse := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) b hbColor hcrit
  obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp hreverse.2
  have hZS : Z T b ≤ stabilizer T (alpha T) :=
    ((sourceGeometry h).omega_bound b hbColor (by
      rw [(sourceGeometry h).distance_constant b hbColor]; exact sourceDistance_pos h)).trans
      (critical_X_le_vertex h e b hbColor (alpha T) hreverse)
  obtain ⟨g,hg⟩ := show x ∈ f.range from (by
    change x ∈ (embedM T).range
    have hxS := hZS hx
    change x ∈ stabilizer T (mVertex T 1) at hxS
    rwa [stabilizer_m_base] at hxS)
  have hgne : g ∉ pCore 2 (L ⊔ R : Subgroup G) := by
    intro hgQ
    apply hxQ
    rw [←hg,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact mem_map_of_mem f hgQ
  have hg2 : g ^ 2 = 1 := by
    apply embedM_injective T
    rw [map_pow,hg,map_one]
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) b hbColor
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hfour := initialMoved_commutator_lower h e hz hk himage g hg2 hgne
  have hUa : (initialMoved L R).map f = U T (alpha T) := by
    rw [graph_U_eq_X_commutator h e hz,graph_X h,graph_component h,←map_commutator]
  have hZa : Z T (alpha T) ≤ V T c := le_iSup_of_le (alpha T) (le_iSup_of_le hac.le le_rfl)
  have hZb : Z T b ≤ V T c := le_iSup_of_le b (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcb]) le_rfl)
  have hcomm : (⁅initialMoved L R,zpowers g⁆).map f ≤ ⁅V T c,V T c⁆ := by
    rw [map_commutator,hUa,MonoidHom.map_zpowers,hg]
    exact commutator_mono ((U_le_Z (alpha T)).trans hZa) (zpowers_le.mpr (hZb hx))
  let := finite_stabilizer T c
  have hVS : V T c ≤ stabilizer T c :=
    ((sourceGeometry h).V_le_Q hb c hc).trans (fun _ hx => hx.1)
  let : Finite (⁅V T c,V T c⁆ : Subgroup (FreeAmalgam T)) :=
    Finite.of_injective (inclusion ((commutator_le_self _).trans hVS)) (inclusion_injective _)
  have hh := card_le_of_le hcomm
  rw [card_map_of_injective (embedM_injective T)] at hh
  exact hfour.trans hh

omit h e hz hk [Finite G] in
private theorem radius_derived_card_eq_base (a : Vertex T) (ha : color T a = false) :
    Nat.card (⁅V T a,V T a⁆ : Subgroup (FreeAmalgam T)) =
      Nat.card (⁅V T (alpha T),V T (alpha T)⁆ : Subgroup (FreeAmalgam T)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  have hv : V T (mVertex T g) = (V T (alpha T)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act T g (alpha T)
  rw [hv,←map_commutator,card_map_of_injective (MulAut.conj g⁻¹).injective]

/-- Every original-group radius has at least four elements in its derived subgroup. -/
theorem radius_derived_card_lower (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) :
    4 ≤ Nat.card (⁅V T a,V T a⁆ : Subgroup (FreeAmalgam T)) := by
  obtain ⟨b,hcrit⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  let p := DistanceEight.PathCentrality.CriticalPath.ofPair (geometry := sourceGeometry h) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans (distance_eq_four h e hz hk himage)
  have hle : 2 ≤ p.walk.length := by omega
  let c := p.walk.getVert 2
  have hc : color T c = false := (p.vertex_color hle).mpr (by decide)
  have hac : (cosetGraph T).dist (alpha T) c = 2 := p.dist_start hle
  have hcb : (cosetGraph T).dist c b = 2 := by rw [p.dist_end,hl]
  have hh := midpoint_derived_card_lower h e hz hk himage b hcrit c hc hac hcb
  rwa [radius_derived_card_eq_base c hc,←radius_derived_card_eq_base a ha] at hh

/-- The moving subgroup retains all these commutators, including their order bound. -/
theorem moving_derived_card_lower (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) :
    4 ≤ Nat.card (_root_.commutator (Vcirc T a)) := by
  have hb : 2 < sourceDistance h := by rw [distance_eq_four h e hz hk himage]; decide
  obtain ⟨g,hga⟩ := exists_mVertex_of_color T ha
  let t := hVertex T g
  have hat : Adjacent T a t := (adjacent_iff_exists_common T a t).mpr ⟨g,Or.inl ⟨hga,rfl⟩⟩
  have hh := radius_derived_card_lower h e hz hk himage a ha
  rw [radius_derived_eq_moving_derived_original h (sourceGeometry h) hb a t ha hat
    (radius_derived_le_fixed h e hz hk himage a ha),←map_subtype_commutator,
    card_map_of_injective (Vcirc T a).subtype_injective] at hh
  exact hh

open Atlas.Codes
/-- Both actual moving quotients contradict the cubic even-image radius. -/
theorem even_image_impossible (himage : (π).range = alternatingGroup (Fin 6)) : False := by
  have hb : 2 < sourceDistance h := by rw [distance_eq_four h e hz hk himage]; decide
  let a := alpha T
  have ha : color T a = false := rfl
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
    a ha (radius_derived_le_fixed h e hz hk himage a ha)
  let := finite_moving (sourceGeometry h) hb a ha
  let := finite_stabilizer T a
  let τ := Offenders.linearize (movingQuotientAction a)
  obtain ⟨b,hcrit⟩ := criticalPair_exists T a ((sourceGeometry h).exists_critical a ha)
  let p := DistanceEight.PathCentrality.CriticalPath.ofPair (geometry := sourceGeometry h) ha hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans (distance_eq_four h e hz hk himage)
  have hle : 2 ≤ p.walk.length := by omega
  let d := p.walk.getVert 2
  have hd : color T d = false := (p.vertex_color hle).mpr (by decide)
  have had : (cosetGraph T).dist a d = 2 := p.dist_start hle
  have hdb : (cosetGraph T).dist d b = 2 := by rw [p.dist_end,hl]
  obtain ⟨f,hf,hr⟩ := cover_projection h e hz hk himage a ha
  let A := (X T b).subgroupOf (stabilizer T a)
  have hAE : A.map f ≤ Atlas.Codes.hexSign.ker := by rw [←hr]; exact map_le_range _ _
  have hcard : Nat.card (A.map f) = 4 := by
    rw [←relIndex_ker,hf]
    have hh := relIndex_map_map_of_injective
      ((Q T a).subgroupOf (stabilizer T a)) A (stabilizer T a).subtype_injective
    have hbcol := critical_endpoint_color T a ha _ hcrit
    have hrev := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
      a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h) b hbcol hcrit
    rw [map_subgroupOf_eq_of_le (critical_X_le_vertex h e b hbcol a hrev),
      map_subgroupOf_eq_of_le (show Q T a ≤ stabilizer T a from fun _ hx => hx.1)] at hh
    exact hh.symm.trans (critical_indices h e hz hk himage a ha b hcrit).1
  have hex : ∃ x, x ∈ A.map f ∧ x ≠ 1 := by
    by_contra! hn
    have he : A.map f = ⊥ := le_bot_iff.mp (fun x hx => hn x hx)
    rw [he,card_bot] at hcard
    omega
  obtain ⟨x,hx,hxn⟩ := hex
  let t : Atlas.Codes.HexEvenAutomorphisms := ⟨x,hAE hx⟩
  have ht : orderOf t = 2 := by
    rw [Subgroup.orderOf_mk]
    let : IsElementaryAbelian 2 (X T b) := omegaCenter_elementary _
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.comap_of_injective
      (stabilizer T a).subtype (stabilizer T a).subtype_injective _
    let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hxn
  have hfull := movingQuotientAction_full_original h (sourceGeometry h) hb a ha
    (radius_derived_le_fixed h e hz hk himage a ha)
  have hn : Nontrivial (Additive ((Vcirc T a) ⧸ center (Vcirc T a))) := by
    by_contra! hh
    let := hh
    have hcomm : IsMulCommutative (Vcirc T a) := ⟨⟨fun x y => by
      have hx : QuotientGroup.mk' (center (Vcirc T a)) x = 1 :=
        Additive.ofMul.injective (Subsingleton.elim _ _)
      exact (mem_center_iff.mp ((QuotientGroup.eq_one_iff x).mp hx) y).symm⟩⟩
    let := hcomm
    have hfour := moving_derived_card_lower h e hz hk himage a ha
    rw [commutator_eq_bot,card_bot] at hfour
    omega
  let := hn
  obtain ⟨q,hq,σ,hσ,hnσ,hσρ,hdegree⟩ := Hexacode.SmallInvolution.exists_residual_model
    f hr.ge
    (by rw [hf]; exact (Q_isPGroup T h.relative_radical.isPGroup
      h.relative_radical.twoCore_le a ha).comap_subtype)
    τ hfull (movingQuotient_fixedSpace_eq_bot_original h (sourceGeometry h) hb a ha
      (radius_derived_le_fixed h e hz hk himage a ha))
    A hAE t ht hx
    (moving_fixedCodim_le_two h e hz hk himage a ha b hcrit d hd had hdb)
  let := hσ
  rcases hdegree with ⟨hcenter,hdim⟩ | ⟨hfσ,hdim⟩
  · let η := (quotientOfLEKer σ (center HexEvenAutomorphisms) hcenter).comp
      Hexacode.even_quotient_center_equiv.symm.toMonoidHom
    have hησ (g : HexEvenAutomorphisms) : η (hexEvenCoordinate g) = σ g := by
      change quotientOfLEKer σ (center HexEvenAutomorphisms) hcenter
        (Hexacode.even_quotient_center_equiv.symm (hexEvenCoordinate g)) = _
      have hh : Hexacode.even_quotient_center_equiv.symm (hexEvenCoordinate g) =
          QuotientGroup.mk' (center HexEvenAutomorphisms) g :=
        Hexacode.even_quotient_center_equiv.symm_apply_eq.mpr rfl
      rw [hh]
      rfl
    have hfη : Function.Injective η := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      rcases (MonoidHom.normal_ker η).eq_bot_or_eq_top with hker | hker
      · exact η.ker_eq_bot_iff.mp hker
      · exfalso
        apply hnσ
        ext g v
        rw [←hησ]
        have hh : hexEvenCoordinate g ∈ η.ker := hker.symm ▸ mem_top _
        exact LinearMap.congr_fun hh v
    obtain ⟨E⟩ := CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace η hfη hdim
    let f := E.groupEquiv.toMonoidHom.comp (hexEvenCoordinate.comp q)
    have hfs : Function.Surjective f := E.groupEquiv.surjective.comp (hexEvenCoordinate_surjective.comp hq)
    have hm : HasNaturalMovingQuotient (L := L) (R := R) a := by
      refine ⟨inferInstance,(alternatingGroup (Fin 6)).subtype.comp f,?_,E.linearEquiv,?_⟩
      · intro x hx
        obtain ⟨g,hg⟩ := hfs ⟨x,hx⟩
        exact ⟨g,congrArg Subtype.val hg⟩
      · intro g v
        rw [←hσρ g v,←hησ]
        exact E.intertwines _ _
    have hlo := moving_derived_card_lower h e hz hk himage a ha
    have hup := moving_derived_card_le_two_of_natural a
      (radius_derived_le_fixed h e hz hk himage a ha) hm
    omega
  · obtain ⟨E,F,hF⟩ := Hexacode.EvenBinaryRecognition.exists_equivariant σ hfσ hσ hdim
    let f := E.toMonoidHom.comp q
    have hfs : Function.Surjective f := E.surjective.comp hq
    have hm : HasHexacodeMovingQuotient (L := L) (R := R) a := by
      refine ⟨inferInstance,hexSign.ker.subtype.comp f,?_,F,?_⟩
      · intro x hx
        obtain ⟨g,hg⟩ := hfs ⟨x,hx⟩
        exact ⟨g,congrArg Subtype.val hg⟩
      · intro g v
        rw [←hσρ g v]
        exact hF _ _
    let := moving_commutative_of_hexacode (sourceGeometry h) (sourceDistance_pos h) a ha
      (radius_derived_le_fixed h e hz hk himage a ha) hm
    have hlo := moving_derived_card_lower h e hz hk himage a ha
    rw [commutator_eq_bot,card_bot] at hlo
    omega


/-- In the cubic initial-kernel branch the original natural action is full symmetric. -/
theorem projection_surjective : Function.Surjective π :=
  (CubicAction.range_alternatives h e hz hk).resolve_left
    (even_image_impossible h e hz hk)

omit hk in
/-- The whole-core alternative retains only the full-symmetric cubic branch. -/
theorem coreExhaustion_or_cubic_fullSymmetric :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧ 2 < sourceDistance h := by
  rcases coreExhaustion_or_cubic_largeDistance h e hz with hx | ⟨hk,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,projection_surjective h e hz hk,hb⟩

omit hk in
/-- Apply the new exclusion to the literal original rank-two classification. -/
theorem rankTwo_or_cubic_fullSymmetric :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧ 2 < sourceDistance h :=
  (coreExhaustion_or_cubic_fullSymmetric h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEven
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
