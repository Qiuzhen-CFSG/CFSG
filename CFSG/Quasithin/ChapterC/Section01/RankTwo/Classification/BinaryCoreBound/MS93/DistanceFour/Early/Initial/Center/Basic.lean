module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Quotient
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Radius centers and their actual central quotients

The center of the radius-two group centralizes the Z-layer at every
M-colored vertex at distance two. The edge centralizer equality therefore
places it in the kernel at that vertex. This is the first observation in
the proof of MS93 (4.6.1).

The binary derived bound and involution generation make V/Z(V) elementary
abelian. We retain the literal action of the full vertex stabilizer and
identify its fixed classes by ambient commutators. No action of the two-core
is discarded. These are preparations, not the center containment in B.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.1), printed pp.900--901.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The radius center is normal in its vertex stabilizer, not in the amalgam. -/
theorem radius_center_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer ((center (V R a)).map (V R a).subtype) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨v, hv, rfl⟩ := hx
  let f := (V R a).normalizerMonoidHom ⟨g, V_normalized a hg⟩
  exact ⟨f v, characteristic_iff_le_comap.mp inferInstance f hv, rfl⟩

/-- The source observation Z(V_a) ≤ Q_c for a vertex c at distance two. -/
theorem radius_center_le_Q_of_dist_two [Finite M]
    (common : CommonFacts R source geometry) (a c : Vertex R)
    (ha : color R a = false) (hd : (cosetGraph R).dist a c = 2) :
    (center (V R a)).map (V R a).subtype ≤ Q R c := by
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hd
  have hc : color R c = false :=
    (color_eq_of_dist_even R a c (by rw [hd]; decide)).symm.trans ha
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases hh : color R t <;> simp_all
  rw [← common.centralizer c t hc hct]
  refine le_inf ((map_subtype_le _).trans
    ((radius_le_Q common a ha).trans (Q_le_adjacent_h R ht hat))) ?_
  rintro x ⟨v, hv, rfl⟩ z hz
  have hZV : Z R c ≤ V R a :=
    le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hd]) le_rfl)
  have hzV : z ∈ V R a := hZV hz
  exact congrArg Subtype.val (mem_center_iff.mp hv ⟨z,hzV⟩)

/-- The radius center lies in every M-colored kernel in its radius-two ball. -/
theorem radius_center_le_Q_of_dist_le_two [Finite M]
    (common : CommonFacts R source geometry) (a c : Vertex R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) :
    (center (V R a)).map (V R a).subtype ≤ Q R c := by
  have he : Even ((cosetGraph R).dist a c) := by
    obtain ⟨p,hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a c
    rw [← hp, walk_even_iff_color_eq, ha, hc]
  by_cases hzero : (cosetGraph R).dist a c = 0
  · have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
    subst c
    exact (map_subtype_le _).trans (radius_le_Q common a ha)
  · apply radius_center_le_Q_of_dist_two common a c ha
    obtain ⟨n, hn⟩ := he
    omega

/-- The literal quotient by the whole radius center is elementary abelian. -/
theorem radiusCenterQuotient_elementary [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) :
    IsElementaryAbelian 2 ((V R a) ⧸ center (V R a)) := by
  let := radiusZ_normal common a ha
  let hE := radiusQuotient_elementary common hb a ha
  have hZ : (Z R a).subgroupOf (V R a) ≤ center (V R a) := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := Z_le_radius_center common a ha hx
    have heq' : y = x := Subtype.ext heq
    subst y
    exact hy
  have hD : _root_.commutator (V R a) ≤ center (V R a) := by
    intro x hx
    apply hZ
    apply radius_derived_le_Z common hb a ha
    rw [← map_subtype_commutator]
    exact mem_map_of_mem (V R a).subtype hx
  let : IsMulCommutative ((V R a) ⧸ center (V R a)) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hD
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro w
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center (V R a)) w
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply hZ
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' ((Z R a).subgroupOf (V R a)) (x ^ 2) = 1
  rw [map_pow]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p _

/-- Conjugation by the whole vertex stabilizer on the radius group. -/
noncomputable def radiusAction (a : Vertex R) :
    stabilizer R a →* MulAut (V R a) :=
  (V R a).normalizerMonoidHom.comp (inclusion (V_normalized a))

/-- The radius action is the ambient conjugation action. -/
theorem radiusAction_apply (a : Vertex R) (g : stabilizer R a) (v : V R a) :
    (radiusAction a g v : FreeAmalgam R) =
      g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ := rfl

/-- The stabilizer action on the source quotient V/Z(V). -/
noncomputable def radiusCenterQuotientAction (a : Vertex R) :
    stabilizer R a →* MulAut ((V R a) ⧸ center (V R a)) :=
  (quotientAut (center (V R a))).comp (radiusAction a)

/-- The central quotient action agrees with conjugation on representatives. -/
theorem radiusCenterQuotientAction_apply (a : Vertex R)
    (g : stabilizer R a) (v : V R a) :
    radiusCenterQuotientAction a g (QuotientGroup.mk' (center (V R a)) v) =
      QuotientGroup.mk' (center (V R a)) (radiusAction a g v) :=
  quotientAut_apply_mk _ _ _

/-- A class is fixed exactly when its actual commutator lies in the radius center. -/
theorem radiusCenterQuotientAction_fixed_iff (a : Vertex R)
    (g : stabilizer R a) (v : V R a) :
    radiusCenterQuotientAction a g (QuotientGroup.mk' (center (V R a)) v) =
      QuotientGroup.mk' (center (V R a)) v ↔
      ⁅(g : FreeAmalgam R), (v : FreeAmalgam R)⁆ ∈
        (center (V R a)).map (V R a).subtype := by
  rw [radiusCenterQuotientAction_apply]
  constructor
  · intro h
    refine ⟨radiusAction a g v / v, QuotientGroup.eq_iff_div_mem.mp h, ?_⟩
    change (radiusAction a g v : FreeAmalgam R) / (v : FreeAmalgam R) = _
    rw [radiusAction_apply, div_eq_mul_inv, commutatorElement_def]
  · rintro ⟨z,hz,heq⟩
    apply QuotientGroup.eq_iff_div_mem.mpr
    have heq' : z = radiusAction a g v / v := by
      apply Subtype.ext
      change (z : FreeAmalgam R) =
        (radiusAction a g v : FreeAmalgam R) / (v : FreeAmalgam R)
      rw [radiusAction_apply, div_eq_mul_inv]
      exact heq
    subst z
    exact hz

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
