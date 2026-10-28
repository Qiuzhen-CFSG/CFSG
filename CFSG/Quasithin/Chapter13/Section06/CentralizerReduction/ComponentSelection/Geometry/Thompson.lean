module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Seeds
public import GorensteinWalter.Section2.Bender1970_18
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.BaumannMap
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The internal module and Thompson reduction in 13.6.9

The Sylow-central seed gives a faithful quotient with trivial two-core.
Characteristic two places its normal closure in the elementary omega-center
of the two-core. If J(T_v) centralizes that closure, Baumann heredity and
Frattini give a supplement inside M_v; this would normalize V_v. The
contradiction yields both the Sylow and global Thompson images, and the
maximum-elementary-subgroup bound constructs a genuine FF-offender.

The geometric nonnormality conclusion of 13.6.8 remains an explicit input
here. This module is the downstream branch, not an assembly of 13.6.8–9.
Source: Aschbacher–Smith, combined manuscript, printed p.928; B.2.3–7,
B.2.11–14 on pp.74–78.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Subgroup Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The normal closure, viewed inside the actual element centralizer. -/
def internalUv (z v : G) : Subgroup (Gv v) := (Uv z v).subgroupOf (Gv v)

instance (z v : G) : (internalUv z v).Normal :=
  normal_subgroupOf_of_le_normalizer (Gv_normalizes_Uv z v)

/-- The star kernel is the centralizer of the internal module. -/
theorem starMk_ker_internal (z v : G) (hz : z ∈ Gv v) :
    (starMk z v).ker = centralizer (internalUv z v : Set (Gv v)) := by
  rw [starMk_ker]
  ext g
  constructor
  · intro hg u hu
    exact Subtype.ext (hg u hu)
  · intro hg u hu
    exact congrArg Subtype.val (hg ⟨u, Uv_le_Gv z v hz hu⟩ hu)

/-- The Sylow-central seed already forces the star quotient to be two-reduced.
No characteristic-two or module assumption is needed for this assertion. -/
theorem Gstar_twoCore_eq_bot [Finite G] (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    pCore 2 (Gstar z v) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hSylow
  let Pstar : Sylow 2 (Gstar z v) := P.mapSurjective (starMk_surjective z v)
  have hcore : pCore 2 (Gstar z v) ≤ (Pstar : Subgroup (Gstar z v)) :=
    pCore_isPGroup.le_sylow_of_normal Pstar
  apply normal_star_subgroup_eq_bot_of_centralizes_seed
  rintro g ⟨x, hx, rfl⟩
  obtain ⟨t, ht, he⟩ := hcore hx
  have htT : (t : G) ∈ Tv T v := hP ▸ mem_map_of_mem (Gv v).subtype ht
  have hez := congrArg (fun a : Gstar z v =>
    ((starAction z v a ⟨z, z_mem_Uv z v⟩ : Uv z v) : G)) he
  change (t : G) * z * (t : G)⁻¹ = (x : G) * z * (x : G)⁻¹ at hez
  have htfix : (t : G) * z * (t : G)⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp (hz htT)]
    simp [mul_assoc]
  exact mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (hez.symm.trans htfix))

private theorem centralizer_twoCore_le [Finite G]
    (hf : Theory.GroupTheory.generalizedFitting G = pCore 2 G) :
    centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
  have hbridge : GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) ≤
      Theory.GroupTheory.generalizedFitting G := by
    apply sup_le
    · apply le_trans _ (Theory.GroupTheory.fitting_le_generalizedFitting G)
      exact le_sSup ⟨fittingSubgroupOf_normal _ inferInstance,
        GorensteinWalter.fittingSubgroupOf_isNilpotent _⟩
    · apply sSup_le
      intro E hE
      have hsub : E.IsSubnormal := by
        have hh := hE.2.1.map (show Function.Surjective (⊤ : Subgroup G).subtype from
          fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
        simpa only [map_subgroupOf_eq_of_le (show E ≤ ⊤ from le_top)] using hh
      exact Theory.GroupTheory.component_le_generalizedFitting G E
        ⟨hsub, (Theory.GroupTheory.isQuasisimple_def E).mpr hE.2.2.2⟩
  rw [hf] at hbridge
  exact (centralizer_le hbridge).trans
    (GorensteinWalter.fstar_self_centralizing.trans hbridge)

/-- The part of B.2.14 used in 13.6: the actual span lies in Ω₁(Z(Q_v)). -/
theorem Uv_le_coreOmega [Finite G] (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    Uv z v ≤ omegaOneCenterAmbient (Qv v) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hSylow
  have hzmem := (mem_omegaOneCenterAmbient_iff (Tv T v) z).mp hz
  have hzG : z ∈ Gv v := hzmem.1.2
  let W := omegaOneCenterAmbient (pCore 2 (Gv v))
  have hWnormal : W.Normal := by
    let Q := pCore 2 (Gv v)
    let C := center Q
    let A := omega₁ C (p := 2)
    let E := A.map C.subtype
    let : A.Characteristic := omega₁_characteristic C
    let : E.Characteristic := characteristic_of_characteristic_of_characteristic
    exact ConjAct.normal_of_characteristic_of_normal
  let := hWnormal
  have hzW : (⟨z, hzG⟩ : Gv v) ∈ W := by
    have hzC : (⟨z, hzG⟩ : Gv v) ∈ centralizer (pCore 2 (Gv v) : Set (Gv v)) := by
      intro q hq
      apply Subtype.ext
      exact hzmem.2.2 q (hP ▸ mem_map_of_mem (Gv v).subtype
        (pCore_isPGroup.le_sylow_of_normal P hq))
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨centralizer_twoCore_le hf hzC, Subtype.ext hzmem.2.1, hzC⟩
  have hspan : Uv z v ≤ W.map (Gv v).subtype := by
    apply conjugateSpanBy_le (Z := zpowers z) (H := Gv v)
      (zpowers_le.mpr (show z ∈ W.map (Gv v).subtype from
        ⟨⟨z, hzG⟩, hzW, rfl⟩))
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le W)).mp
    change ((W.map (Gv v).subtype).comap (Gv v).subtype).Normal
    rw [comap_map_eq_self_of_injective (Gv v).subtype_injective]
    infer_instance
  have hmap : W.map (Gv v).subtype = omegaOneCenterAmbient (Qv v) :=
    (omegaOneCenterAmbient_map_injective (Gv v).subtype
      (Gv v).subtype_injective (pCore 2 (Gv v))).symm
  exact hspan.trans hmap.le

/-- In particular, the source module is central in the actual ambient two-core. -/
theorem Uv_le_center_Qv [Finite G] (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    Uv z v ≤ (center (Qv v)).map (Qv v).subtype := by
  intro u hu
  obtain ⟨huQ, _, hc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp
    (Uv_le_coreOmega T z v hSylow hz hf hu)
  exact ⟨⟨u, huQ⟩, mem_center_iff.mpr (fun q => Subtype.ext (hc q q.property)), rfl⟩

/-- Elementary abelianity of the internal module is obtained from the core. -/
theorem internalUv_elementary [Finite G] (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    IsElementaryAbelian 2 (internalUv z v) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv v)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hle := Uv_le_coreOmega T z v hSylow hz hf
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : omegaOneCenterAmbient (Qv v) => (w : G))
      (mul_comm (⟨x, hle x.property⟩ : omegaOneCenterAmbient (Qv v))
        ⟨y, hle y.property⟩)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) ((x : Gv v) : G) (hle x.property)))

/-- Two-reducedness in the literal centralizer quotient of the internal
normal elementary subgroup, as in Definition B.2.11. -/
theorem internalUv_twoReduced [Finite G] (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzG : z ∈ Gv v) (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    pCore 2 (Gv v ⧸ centralizer (internalUv z v : Set (Gv v))) = ⊥ := by
  have hk : (uvAction z v).ker = centralizer (internalUv z v : Set (Gv v)) :=
    (QuotientGroup.ker_mk' (uvAction z v).ker).symm.trans (starMk_ker_internal z v hzG)
  let e : Gstar z v ≃* (Gv v ⧸ centralizer (internalUv z v : Set (Gv v))) :=
    QuotientGroup.congr _ _ (MulEquiv.refl (Gv v)) (by simpa using hk)
  have he := pCore_map_iso 2 e
  rw [Gstar_twoCore_eq_bot T z v hSylow hz, Subgroup.map_bot] at he
  exact he.symm

/-- The faithful binary action on the source internal module. -/
noncomputable def uvRepresentation (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)] :
    Representation (ZMod 2) (Gstar z v) (Additive (internalUv z v)) :=
  Representation.NormalElementaryQuotient.representation
    (internalUv z v) (starMk z v) (starMk_surjective z v) (starMk_ker_internal z v hz)

theorem uvRepresentation_faithful (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)] :
    Function.Injective (uvRepresentation z v hz) :=
  Representation.NormalElementaryQuotient.representation_injective
    (internalUv z v) (starMk z v) (starMk_surjective z v) (starMk_ker_internal z v hz)

/-- On representatives the linear action is the original ambient conjugation. -/
theorem uvRepresentation_apply (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)]
    (g : Gv v) (u : Additive (internalUv z v)) :
    (((uvRepresentation z v hz (starMk z v g) u).toMul : Gv v) : G) =
      (g : G) * ((u.toMul : Gv v) : G) * (g : G)⁻¹ :=
  congrArg (Gv v).subtype (Representation.NormalElementaryQuotient.representation_apply
    (internalUv z v) (starMk z v) (starMk_surjective z v) (starMk_ker_internal z v hz) g u)

/-- Agreement of the two named actions at every element of the exact quotient. -/
theorem uvRepresentation_eq_starAction (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)] (g : Gstar z v)
    (u : Additive (internalUv z v)) :
    (((uvRepresentation z v hz g u).toMul : Gv v) : G) =
      (starAction z v g ⟨((u.toMul : Gv v) : G), u.toMul.property⟩ : G) := by
  obtain ⟨x, rfl⟩ := starMk_surjective z v g
  rw [uvRepresentation_apply, starAction_mk_apply]

private theorem baumann_frattini [Finite G] (P : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hJ : elementaryAbelianMaxJ (P : Subgroup G) ≤ centralizer (U : Set G)) :
    normalizer (ChapterB.baumann (P : Subgroup G) : Set G) ⊔ centralizer (U : Set G) = ⊤ := by
  let C := centralizer (U : Set G)
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal C
  have hRmap : (R : Subgroup C).map C.subtype = (P : Subgroup G) ⊓ C := by
    rw [hR, subgroupOf_map_subtype]
  have hB : ChapterB.baumann (P : Subgroup G) = ChapterB.baumann ((P : Subgroup G) ⊓ C) :=
    ChapterB.lemma_B_2_3_5 _ U ((IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal P) hJ
  have hN : normalizer ((R : Subgroup C).map C.subtype : Set G) ≤
      normalizer (ChapterB.baumann (P : Subgroup G) : Set G) := by
    rw [hRmap, hB]
    exact normalizer_le_normalizer_baumann _
  exact top_unique (R.normalizer_sup_eq_top.symm.le.trans (sup_le_sup_right hN C))

/-- The source Frattini argument: centralizing J(T_v) would normalize V_v.
The normalizer bound is precisely 13.6.5; the geometric branch supplies
normalization by M_v and the contrary relative nonnormality. -/
theorem sylowThompson_star_ne_bot [Finite G] (L T M S : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (internalUv z v)]
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hS : S = ChapterB.baumann (Tv T v))
    (hcontrol : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (hMv : Mv M v ≤ normalizer (Vv L z v : Set G))
    (hnormal : ¬ ((Vv L z v).subgroupOf (Gv v)).Normal) :
    starImage z v (elementaryAbelianMaxJ (Tv T v)) ≠ ⊥ := by
  intro hbot
  obtain ⟨P, hP⟩ := hSylow
  have hJ : elementaryAbelianMaxJ (P : Subgroup (Gv v)) ≤
      centralizer (internalUv z v : Set (Gv v)) := by
    rw [← starMk_ker_internal z v hz]
    have he : (elementaryAbelianMaxJ (Tv T v)).subgroupOf (Gv v) =
        elementaryAbelianMaxJ (P : Subgroup (Gv v)) := by
      rw [← hP, elementaryAbelianMaxJ_map_injective (Gv v).subtype
        (Gv v).subtype_injective]
      exact comap_map_eq_self_of_injective (Gv v).subtype_injective _
    exact (Subgroup.map_eq_bot_iff _).mp (by simpa only [starImage, he] using hbot)
  have hfr := baumann_frattini P (internalUv z v) hJ
  have hB : (ChapterB.baumann (P : Subgroup (Gv v))).map (Gv v).subtype = S := by
    rw [hS]
    exact (baumann_map_injective (Gv v).subtype (Gv v).subtype_injective _).trans
      (congrArg ChapterB.baumann hP)
  have hn : (normalizer (ChapterB.baumann (P : Subgroup (Gv v)) : Set (Gv v))).map
      (Gv v).subtype ≤ normalizer (Vv L z v : Set G) := by
    apply le_trans _ hMv
    apply le_trans _ hcontrol
    apply le_inf (map_subtype_le _)
    have hh := (ChapterB.baumann (P : Subgroup (Gv v))).le_normalizer_map (Gv v).subtype
    rwa [hB] at hh
  have hc : (centralizer (internalUv z v : Set (Gv v))).map (Gv v).subtype ≤
      normalizer (Vv L z v : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer (Vv L z v : Set G))
    rintro g ⟨x, hx, rfl⟩
    have hk : x ∈ (starMk z v).ker := by rwa [starMk_ker_internal z v hz]
    rw [starMk_ker] at hk
    exact centralizer_le (Vv_le_Uv L z v) hk
  apply hnormal
  apply normal_subgroupOf_of_le_normalizer
  have hh := congrArg (fun K : Subgroup (Gv v) => K.map (Gv v).subtype) hfr
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh ▸ sup_le hn hc

/-- The global Thompson image is nontrivial because the Sylow Thompson
subgroup maps into J(G_v). These two subgroups are not identified. -/
theorem globalThompson_star_ne_bot [Finite G] (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hJ : starImage z v (elementaryAbelianMaxJ (Tv T v)) ≠ ⊥) :
    starImage z v (elementaryAbelianMaxJ (Gv v)) ≠ ⊥ := by
  obtain ⟨P, hP⟩ := hSylow
  have hle : elementaryAbelianMaxJ (Tv T v) ≤ elementaryAbelianMaxJ (Gv v) := by
    have hh := map_mono (f := (Gv v).subtype) (elementaryAbelianMaxJ_sylow_le_top P)
    rw [← elementaryAbelianMaxJ_map_injective (Gv v).subtype (Gv v).subtype_injective,
      ← elementaryAbelianMaxJ_map_injective (Gv v).subtype (Gv v).subtype_injective,
      hP, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  intro he
  apply hJ
  exact eq_bot_iff.mpr (he ▸ map_mono (comap_mono hle))

/-- The nontrivial J(G_v) image gives an actual offender for the faithful
binary representation used in B.5.6. -/
theorem uvRepresentation_isFF [Finite G] (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)]
    (hJ : starImage z v (elementaryAbelianMaxJ (Gv v)) ≠ ⊥) :
    Representation.BinaryOffender.IsFFModule (uvRepresentation z v hz) := by
  apply Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    (internalUv z v) (starMk z v) (starMk_surjective z v) (starMk_ker_internal z v hz)
    (⊤ : Subgroup (Gv v)) le_top
  intro hle
  apply hJ
  have he : (elementaryAbelianMaxJ (Gv v)).subgroupOf (Gv v) =
      elementaryAbelianMaxJ (⊤ : Subgroup (Gv v)) := by
    have hh := elementaryAbelianMaxJ_map_injective (Gv v).subtype
      (Gv v).subtype_injective (⊤ : Subgroup (Gv v))
    rw [← MonoidHom.range_eq_map, range_subtype] at hh
    rw [hh]
    exact comap_map_eq_self_of_injective (Gv v).subtype_injective _
  exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [he] using hle)

/-- The complete Thompson branch, with the geometric nonnormality input
kept visible for final assembly. The earlier inputs are the Sylow assertion,
central involution, 13.6.4, normalizer control 13.6.5 and characteristic two
13.6.6. All module and offender witnesses are constructed above. -/
theorem thompson_reduction_of_nonnormal [Finite G]
    (L T M S : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hS : S = ChapterB.baumann (Tv T v))
    (hcontrol : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (hMv : Mv M v ≤ normalizer (Vv L z v : Set G))
    (hnormal : ¬ ((Vv L z v).subgroupOf (Gv v)).Normal) :
    Uv z v ≤ omegaOneCenterAmbient (Qv v) ∧
      pCore 2 (Gstar z v) = ⊥ ∧
      ∃ hE : IsElementaryAbelian 2 (internalUv z v),
        let := hE
        let hzG := ((mem_omegaOneCenterAmbient_iff (Tv T v) z).mp hz).1.2
        Function.Injective (uvRepresentation z v hzG) ∧
          starImage z v (elementaryAbelianMaxJ (Tv T v)) ≠ ⊥ ∧
          starImage z v (elementaryAbelianMaxJ (Gv v)) ≠ ⊥ ∧
          Representation.BinaryOffender.IsFFModule (uvRepresentation z v hzG) := by
  have hzmem := (mem_omegaOneCenterAmbient_iff (Tv T v) z).mp hz
  have hzcent : Tv T v ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzmem.2.2 t ht)
  let hE := internalUv_elementary T z v hSylow hz hf
  let := hE
  have hJ := sylowThompson_star_ne_bot L T M S z v hzmem.1.2 hSylow hS hcontrol hMv hnormal
  have hJG := globalThompson_star_ne_bot T z v hSylow hJ
  exact ⟨Uv_le_coreOmega T z v hSylow hz hf,
    Gstar_twoCore_eq_bot T z v hSylow hzcent, hE,
    uvRepresentation_faithful z v hzmem.1.2, hJ, hJG,
    uvRepresentation_isFF z v hzmem.1.2 hJG⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
