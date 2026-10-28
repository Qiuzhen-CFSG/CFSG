module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictOrbit
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.GroupTheory.ConjugationLocalGeometry
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual crossing subgroups in the strict recognition branch

A cubic in the natural Sylow normalizer belongs to O²(N_L(Z_S)) and
moves the chosen involution. Its conjugate Frattini line is disjoint
from the original line, so E = U ∩ U^d is elementary abelian. The
literal crossing centralizer X = C_{U^d}(Z_S) has elementary dotted
image, since its squares lie in the conjugate Frattini line inside U.

Two natural hyperplanes, U ∩ V and U^d ∩ V, generate V. The first
vanishes in the dotted action and the second belongs to X. This proves
V-dot ≤ X-dot directly, retaining the original quotient map and right
conjugation U^d = d⁻¹Ud. No order for O₂(H) is assumed.

Source: Aschbacher--Smith, 6.2.17(4),(9) and the elementary actor in
6.2.18, printed pp.689--690. The remaining crossing geometry and strict
contradiction stay with qt-d-1222-recognition-strict-elimination;
LocalAnalysis is discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

@[expose] def strictCrossingResidual (T L R : Subgroup G) : Subgroup G :=
  let N := L ⊓ normalizer (ZS T L R : Set G)
  (pResidual 2 N).map N.subtype

@[expose] def strictCrossingIntersection (T L R : Subgroup G) (z d : G) : Subgroup G :=
  sourceClosure T L R z ⊓ (sourceClosure T L R z).map (MulAut.conj d⁻¹).toMonoidHom

@[expose] def strictCrossingGroup (T L R : Subgroup G) (z d : G) : Subgroup G :=
  (sourceClosure T L R z).map (MulAut.conj d⁻¹).toMonoidHom ⊓
    centralizer (ZS T L R : Set G)

@[expose] def strictCrossingImage (T L R : Subgroup G) (z d : G) :
    Subgroup (StrictActor T L R z) :=
  ((strictCrossingGroup T L R z d).subgroupOf (centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (strictQuotientAction T L R z).ker)

/-- A source cubic lies in the two-residual of the plane normalizer and moves z. -/
theorem strict_exists_crossing_cubic
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2) :
    ∃ d ∈ strictCrossingResidual (T : Subgroup G) L R,
      d ∈ L ∧ d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G) ∧
      d ∈ normalizer (ZS (T : Subgroup G) L R : Set G) ∧
      orderOf d = 3 ∧ d ∉ centralizer ({z} : Set G) := by
  obtain ⟨d, hdL, hdS, hd⟩ := exists_cubic_in_layer_sylow_normalizer h611 hnatural
  have hdV : d ∈ normalizer (layer L R : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural.2.1
    exact hm.normalizes hdL
  have hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := by
    change d ∈ normalizer (layer L R ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) : Set G)
    apply inf_normalizer_le_normalizer_inf
    constructor
    · exact hdV
    · exact normalizer_le_normalizer_centralizer ((T : Subgroup G) ⊓ L) hdS
  let N := L ⊓ normalizer (ZS (T : Subgroup G) L R : Set G)
  have hdN : d ∈ N := ⟨hdL, hdZ⟩
  have hres : (⟨d, hdN⟩ : N) ∈ pResidual 2 N :=
    mem_pResidual_of_orderOf_coprime (by rw [Subgroup.orderOf_mk, hd]; decide)
  have hnot : d ∉ centralizer ({z} : Set G) := by
    intro hh
    have hfix : d * z * d⁻¹ = z :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
    have hz1 : z = 1 := hnatural.2.1.cubic_fixed_eq_one hdL hd
      (show z ∈ layer L R from hz.1) hfix
    have : orderOf z ≠ 2 := by rw [hz1, orderOf_one]; decide
    exact this horder
  exact ⟨d, ⟨⟨d, hdN⟩, hres, rfl⟩, hdL, hdS, hdZ, hd, hnot⟩

omit [Finite G] in
/-- Every genuine moving plane conjugator displaces the Frattini line. -/
theorem strict_disjoint_conjugate_line
    (horder : orderOf z = 2) {d : G}
    (hd : d ∉ centralizer ({z} : Set G)) :
    Disjoint (zpowers z) ((zpowers z).map (MulAut.conj d⁻¹).toMonoidHom) := by
  apply disjoint_iff.mpr
  apply inf_eq_bot_of_card_two_of_ne _ _
    ((Nat.card_zpowers z).trans horder)
    ((card_map_of_injective (MulAut.conj d⁻¹).injective).trans
      ((Nat.card_zpowers z).trans horder))
  intro he
  have hi : d⁻¹ ∈ normalizer (zpowers z : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr he.symm
  have hc := normalizer_le_centralizer_of_card_two (zpowers z)
    ((Nat.card_zpowers z).trans horder) ((normalizer (zpowers z : Set G)).inv_mem hi)
  apply hd
  exact mem_centralizer_singleton_iff.mpr (by
    simpa only [inv_inv] using (mem_centralizer_iff.mp hc z (mem_zpowers z)).symm)

/-- The source plane belongs to the actual intersection U ∩ U^d. -/
theorem strict_plane_le_crossing
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) {d : G}
    (hd : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    ZS (T : Subgroup G) L R ≤ strictCrossingIntersection (T : Subgroup G) L R z d := by
  have hle := (ZS_le_sourceClosure_intersection h611 hz).trans inf_le_left
  refine le_inf hle ?_
  have he := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (ZS (T : Subgroup G) L R : Set G)).inv_mem hd)
  rw [← he]
  exact map_mono hle

/-- The crossed intersection itself, before taking the central quotient, is elementary. -/
theorem LocalAnalysis.strict_crossing_elementary
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hd : d ∉ centralizer ({z} : Set G)) :
    IsElementaryAbelian 2 (strictCrossingIntersection (T : Subgroup G) L R z d) := by
  let U := sourceClosure (T : Subgroup G) L R z
  have hp : IsPGroup 2 U :=
    ((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core
  have hphi := (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1
  let : Fact (IsPGroup 2 (strictCrossingIntersection (T : Subgroup G) L R z d)) :=
    ⟨hp.to_le inf_le_left⟩
  apply frattini_eq_bot_iff_isElementaryAbelian.mp
  apply frattini_eq_bot_of_disjoint_images hp (hp.map (MulAut.conj d⁻¹).toMonoidHom)
    (show strictCrossingIntersection (T : Subgroup G) L R z d ≤ U from inf_le_left)
    (show strictCrossingIntersection (T : Subgroup G) L R z d ≤ U.map _ from inf_le_right)
  rw [frattini_image_map _ _ (MulAut.conj d⁻¹).injective, hphi]
  exact strict_disjoint_conjugate_line horder hd

omit [Finite G] in
/-- The literal crossing centralizer belongs to H. -/
theorem strictCrossingGroup_le_centralizer (T L R : Subgroup G) (z d : G)
    (hz : z ∈ ZS T L R) :
    strictCrossingGroup T L R z d ≤ centralizer ({z} : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hx.2 z hz).symm

/-- E lies in X because E is elementary and contains the source plane. -/
theorem LocalAnalysis.strict_crossing_le_group
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    strictCrossingIntersection (T : Subgroup G) L R z d ≤
      strictCrossingGroup (T : Subgroup G) L R z d := by
  let E := strictCrossingIntersection (T : Subgroup G) L R z d
  let := A.strict_crossing_elementary h611 hnatural hz horder hstrict hd
  refine le_inf inf_le_right ?_
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm (⟨y, strict_plane_le_crossing h611 hz hdZ hy⟩ : E) ⟨x, hx⟩)


/-- The natural hyperplanes from U and U^d generate the whole layer. -/
theorem LocalAnalysis.strict_layer_generated_by_crossing
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (_hz : z ∈ ZS (T : Subgroup G) L R)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdL : d ∈ L)
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    let U := sourceClosure (T : Subgroup G) L R z
    (U ⊓ layer L R) ⊔ (U.map (MulAut.conj d⁻¹).toMonoidHom ⊓ layer L R) = layer L R := by
  let U := sourceClosure (T : Subgroup G) L R z
  let V := layer L R
  let B := U ⊓ V
  let f := (MulAut.conj d⁻¹).toMonoidHom
  have hdV : d ∈ normalizer (V : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural.2.1
    exact hm.normalizes hdL
  have hVm : V.map f = V := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V : Set G)).inv_mem hdV)
  have hBm : B.map f = U.map f ⊓ V := by
    rw [map_inf _ _ _ (MulAut.conj d⁻¹).injective, hVm]
  have hBcard : Nat.card B = 8 := (A.strict_intersection_eq_core h611 hnatural hstrict).2
  have hinter : B ⊓ B.map f = ZS (T : Subgroup G) L R :=
    (h611.natural_eight_cubic_geometry hnatural.2.1 B inf_le_right hBcard
      hstrict.le hdL hdS hd).2
  have hBV : B.map f ≤ V := hBm ▸ inf_le_right
  let := h611.layer_elementary
  have hn : B.map f ≤ normalizer (B : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx b hb
    exact congrArg Subtype.val (mul_comm (⟨b, hb.2⟩ : V) ⟨x, hBV hx⟩)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B (B.map f) hn
  rw [card_map_of_injective (MulAut.conj d⁻¹).injective, hBcard, hinter,
    (h611.natural_ZS_geometry hnatural).2.1] at hc
  have he : B ⊔ B.map f = V :=
    eq_of_le_of_card_ge (sup_le inf_le_right hBV) (by rw [hnatural.2.1.card]; omega)
  rwa [hBm] at he

/-- The original U is contained in the kernel of its dotted action. -/
theorem LocalAnalysis.strict_closure_le_dotted_kernel
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (sourceClosure (T : Subgroup G) L R z).subgroupOf (centralizer ({z} : Set G)) ≤
      (strictQuotientAction (T : Subgroup G) L R z).ker := by
  intro u hu
  apply A.strict_core_le_action_kernel h611 hnatural hz horder hstrict
  obtain ⟨v, hv, he⟩ := A.closure_le_core hu
  exact (Subtype.ext he : v = u) ▸ hv

/-- Source 6.2.17(9), with both images taken under the literal dotted quotient. -/
theorem LocalAnalysis.strict_layerImage_le_crossingImage
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdL : d ∈ L)
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    strictLayerImage (T : Subgroup G) L R z ≤ strictCrossingImage (T : Subgroup G) L R z d := by
  let H := centralizer ({z} : Set G)
  let U := sourceClosure (T : Subgroup G) L R z
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  let D := (strictCrossingImage (T : Subgroup G) L R z d).comap q
  have hVD : layer L R ≤ D.map H.subtype := by
    rw [← A.strict_layer_generated_by_crossing h611 hnatural hz hstrict hdL hdS hd]
    apply sup_le
    · intro v hv
      let vH : H := ⟨v, layer_le_involution_centralizer h611 hz hv.2⟩
      refine ⟨vH, ?_, rfl⟩
      have hk : vH ∈ (strictQuotientAction (T : Subgroup G) L R z).ker :=
        A.strict_closure_le_dotted_kernel h611 hnatural hz horder hstrict hv.1
      change q vH ∈ strictCrossingImage (T : Subgroup G) L R z d
      have he : q vH = 1 := (QuotientGroup.eq_one_iff vH).mpr hk
      rw [he]
      exact one_mem _
    · intro v hv
      have hvX : v ∈ X := ⟨hv.1, h611.layer_centralizes_ZS hv.2⟩
      let vH : H := ⟨v, layer_le_involution_centralizer h611 hz hv.2⟩
      exact ⟨vH, mem_map_of_mem q hvX, rfl⟩
  rintro a ⟨v, hv, rfl⟩
  obtain ⟨w, hw, he⟩ := hVD hv
  exact (Subtype.ext he : w = v) ▸ hw

/-- The actual crossing group has elementary image: its squares lie in
its conjugate Frattini line, which is already inside the original U. -/
theorem LocalAnalysis.strict_crossingImage_elementary
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d) := by
  let U := sourceClosure (T : Subgroup G) L R z
  let H := centralizer ({z} : Set G)
  let f := (MulAut.conj d⁻¹).toMonoidHom
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  let D := strictCrossingImage (T : Subgroup G) L R z d
  have hp : IsPGroup 2 (U.map f) :=
    (((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core).map f
  let : Fact (IsPGroup 2 (U.map f)) := ⟨hp⟩
  have hline : (zpowers z).map f ≤ U := by
    have hh := map_mono (f := f) (zpowers_le.mpr hz)
    have he := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (ZS (T : Subgroup G) L R : Set G)).inv_mem hdZ)
    exact (hh.trans_eq he).trans (hstrict.le.trans inf_le_left)
  have hs (a : D) : a ^ 2 = 1 := by
    obtain ⟨x, hx, hxa⟩ := a.property
    have hxU : (x : G) ∈ U.map f := hx.1
    have hsphi : (x : G) ^ 2 ∈ (frattini (U.map f)).map (U.map f).subtype :=
      ⟨(⟨x, hxU⟩ : U.map f) ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩
    rw [frattini_image_map U f (MulAut.conj d⁻¹).injective,
      (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1] at hsphi
    have hk : x ^ 2 ∈ (strictQuotientAction (T : Subgroup G) L R z).ker :=
      A.strict_closure_le_dotted_kernel h611 hnatural hz horder hstrict (hline hsphi)
    apply Subtype.ext
    change (a : StrictActor (T : Subgroup G) L R z) ^ 2 = 1
    rw [← hxa, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have hinv (a : D) : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs a)
  exact { toIsMulCommutative := ⟨⟨fun a b => by
            calc a * b = (a * b)⁻¹ := (hinv _).symm
                 _ = b * a := by rw [mul_inv_rev, hinv, hinv]⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
