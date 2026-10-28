module

public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.Geometry
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.SylowCore
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.LocalNormalizer.InvolutionCosets
public import Stellmacher.Recognition.Parrott.OuterInvolutionClassSeparation
public import Stellmacher.Recognition.Parrott.SecondNormalizerGrowthLocal
public import Stellmacher.Recognition.Parrott.SylowGenerators
public import Stellmacher.Recognition.Parrott.SylowOuterNormalization
public import Stellmacher.Recognition.Parrott.SylowSeedBxNormalization
public import Stellmacher.Recognition.Parrott.SylowSeedLastNormalization
public import Stellmacher.Recognition.Parrott.SylowSeedLastRelations
public import Stellmacher.Recognition.Parrott.SylowSeedMiddleNormalization
public import Stellmacher.Recognition.Parrott.SylowSeedOuterCentralization
public import Stellmacher.Recognition.Parrott.SylowSeedOuterCompletion
public import Stellmacher.Recognition.Parrott.SylowSeedYdCoset

/-!
# Parrott generators from local inputs: SylowNormalization

Transporting the seed root into the original core identifies the class of
its square; fusion outside the derived core separates this class from its
central twist. This discharges the nonfusion step in (19). The coordinate
adjustments for (16)–(19), together with the existing two-case normalization,
produce a complete Sylow generator frame on the supplied local data.

The derived-core normalizer identity and local normalizer solvability in
`ParrottLocalInputs` replace the ambient N₂ assumption. The original APIs
remain unchanged, and F, the supplied Sylow subgroup, t and v remain literal.

Source: D. Parrott, *A characterization of the Tits simple group* (1972),
§3, printed pp.678–682, with the local geometry of §§1–2.
-/

section

/- OuterInvolutionClassSeparation: local-input version of the original construction. -/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData

variable {G : Type*} [Group G] [Finite G] {z : G}
  {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable (f : ParrottSylowSeedData n false)

/-- A normalizer conjugate of the seed root lies in the original two-core. -/
public theorem x_conjugate_mem_original_core_of_local_inputs
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    ∃ q : normalizer (e.F : Set G), (q : G) * f.x * (q : G)⁻¹ ∈
      (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let X := K.map N.subtype
  let U := omega₁ K (p := 2)
  let W := U.map (N.subtype.comp K.subtype)
  have hxX : f.x ∈ X := f.x_mem_normalizer_core
  have hxW : f.x ∉ W := by
    intro hx
    have hWC : W = X ⊓ centralizer
        ((center U).map ((N.subtype.comp K.subtype).comp U.subtype) : Set G) :=
      n.omega_eq_centralizer
    rw [hWC] at hx
    have hv : n.v ∈ (center U).map ((N.subtype.comp K.subtype).comp U.subtype) := by
      rw [n.omega_center_eq]
      exact mem_sup_right (mem_zpowers n.v)
    have hc : Commute f.x n.v := (mem_centralizer_iff.mp hx.2 n.v hv).symm
    have ht : n.t = 1 := f.relations.eq01_xv.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ho := n.t_order
    rw [ht, orderOf_one] at ho
    norm_num at ho
  have hsqJ : f.x ^ 2 ∉ J.map H.subtype := f.square_not_mem_core h
  have hsq2 : (f.x ^ 2) ^ 2 = 1 := by
    simpa only [← pow_mul] using f.relations.eq01_x
  have hsqOrder : orderOf (f.x ^ 2) = 2 := orderOf_eq_prime hsq2
    (fun heq => hsqJ (heq ▸ (J.map H.subtype).one_mem))
  obtain ⟨q, hq⟩ := e.normalizer_core_involution_transport_of_local_inputs h hlocal n.sylow_lt_normalizer
    n.Q n.core_fixed_le_derived (f.x ^ 2) (X.pow_mem hxX 2) hsq2
  let qN : N := q
  have hqE : (qN : G) * f.x ^ 2 * (qN : G)⁻¹ ∈ E :=
    e.outer_involution_normalizer_conjugate_mem_derived h (f.x ^ 2) hsqJ hsqOrder qN hq
  let a := (qN : G) * f.x * (qN : G)⁻¹
  have haX : a ∈ X := by
    obtain ⟨xN, hxN, hex⟩ := hxX
    refine ⟨qN * xN * qN⁻¹, (inferInstance : K.Normal).conj_mem xN hxN qN, ?_⟩
    change (qN : G) * (xN : G) * (qN : G)⁻¹ = a
    change (xN : G) = f.x at hex
    rw [hex]
  have ha2 : a ^ 2 ∈ E := by
    have heq : a ^ 2 = (qN : G) * f.x ^ 2 * (qN : G)⁻¹ :=
      (map_pow (MulAut.conj (qN : G)) f.x 2).symm
    rwa [heq]
  have hNW : N ≤ normalizer (W : Set G) := by
    let V := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : V.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map (H := V) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, V, W, map_map] using hh
  refine ⟨qN, ?_⟩
  by_contra haJ
  have haW : a ∈ W := e.normalizer_core_outer_square_mem_derived_mem_omega_of_local_inputs h hlocal
    n.sylow_lt_normalizer a haX ha2 haJ
  exact hxW ((mem_normalizer_iff.mp (hNW qN.property) f.x).mpr haW)

/-- The seed square is in the v-class, before equations (17)-(19). -/
public theorem square_isConj_v_of_local_inputs
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    IsConj (f.x ^ 2) n.v := by
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let ZK := (center K).map (N.subtype.comp K.subtype)
  obtain ⟨q, hq⟩ := f.x_conjugate_mem_original_core_of_local_inputs h hlocal
  let α := MulAut.conj (q : G)
  have hsq : (α f.x) ^ 2 ∉ zpowers z := by
    intro hs
    have hsZ : α (f.x ^ 2) ∈ ZK := by
      rw [map_pow]
      exact (zpowers_le.mpr e.z_mem_normalizer_core_center) hs
    have hxZ : f.x ^ 2 ∈ ZK :=
      (mem_normalizer_iff.mp (e.normalizer_core_centers_normalized.1 q.property)
        (f.x ^ 2)).mpr hsZ
    exact f.square_not_mem_core h (e.le_core (e.normalizer_core_center_le hxZ))
  have hv : IsConj ((α f.x) ^ 2) n.v := f.core_square_isConj_v h _ hq hsq
  have hc : IsConj (f.x ^ 2) ((α f.x) ^ 2) := by
    apply isConj_iff.mpr
    exact ⟨(q : G), (map_pow α f.x 2)⟩
  exact hc.trans hv

variable [IsSimpleGroup G]

/-- The central twist of the seed square is in the z-class. -/
public theorem square_mul_z_isConj_z_of_local_inputs
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) : IsConj (f.x ^ 2 * z) z := by
  have hxv := f.square_isConj_v_of_local_inputs h hlocal
  obtain ⟨u, hu2, huH, huE, hzu⟩ := parrott_fusion_outside_derived_of_normalizer hns z h hlocal.derived_normalizer
  have huJ : u ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
    intro huJ
    obtain ⟨l, hl⟩ := n.original_core_fusion u huJ huE hu2
    exact n.not_isConj (hzu.trans (isConj_iff.mpr ⟨(l : G), hl⟩).symm)
  obtain ⟨a, ha⟩ := parrott_outer_involution_classes z h (f.x ^ 2 * z) u
    (e.sylow_le_centralizer f.square_mul_z_mem_sylow)
    (f.square_mul_z_not_mem_core h) (f.square_mul_z_order h) huH huJ hu2
  rcases ha with ha | ha
  · exact (hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).symm
  · have htwist : (f.x ^ 2 * z) * z = f.x ^ 2 := by
      rw [mul_assoc, ← pow_two, show z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one z]
      simp
    exact (n.not_isConj
      ((hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).trans (by simpa only [htwist] using hxv))).elim

/-- No element of C_G(z) fuses the two outer seed involutions. -/
public theorem square_mul_z_nonfusion_of_local_inputs
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    ∀ q : centralizer ({z} : Set G),
      (q : G) * (f.x ^ 2 * z) * (q : G)⁻¹ ≠ (f.x ^ 2 * z) * z := by
  intro q hq
  have htwist : (f.x ^ 2 * z) * z = f.x ^ 2 := by
    rw [mul_assoc, ← pow_two, show z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one z]
    simp
  exact n.not_isConj ((f.square_mul_z_isConj_z_of_local_inputs hns hlocal h).symm.trans
    ((isConj_iff.mpr ⟨(q : G), by simpa only [htwist] using hq⟩).trans
      (f.square_isConj_v_of_local_inputs h hlocal)))

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowSeedLastRelations: local-input version of the original construction. -/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
  {n : ParrottNormalizerFusionData e}
variable (f : ParrottSylowSeedData n false)

/-- The established seed nonfusion theorem discharges the local class input.
Only the commutator-coset alternative remains to select this central factor. -/
public theorem eq19_yc_of_alternative_of_local_inputs [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) (hm : f.OuterMiddleRelations)
    (halt : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t ∨
      Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z) :
    Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z :=
  f.eq19_yc_of_alternative_of_nonfusion hm (f.square_mul_z_nonfusion_of_local_inputs hns hlocal h) halt

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowSeedLastNormalization: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- A further choice of core coordinates completes (19), leaving the central
factor in the d-equation for the final x ↦ xt correction. -/
public theorem exists_outer_last_normalization_of_local_inputs [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (f : ParrottSylowSeedData n false) (hm : f.OuterMiddleRelations)
    (hyc : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z) :
    ∃ g : ParrottSylowSeedData n false, g.OuterMiddleRelations ∧ g.OuterLastRelations := by
  have hz : z ≠ 1 := (orderOf_eq_prime_iff.mp h.involution).2
  obtain ⟨hb, hc, hd⟩ := f.outer_discrepancies_mem_derived h
  obtain ⟨_, ⟨ci,cj,ck,hc⟩, ⟨di,dj,dk,hd⟩⟩ :=
    f.relations.outer_image_parameters hz hm.eq16_ax hb hc hd
  have halt := f.relations.last_image_alternatives hz hm.eq16_ax hm.eq18_bx
    hyc hm.eq17_yd ci cj ck di dj dk hc hd
  rcases f.relations.normalize_last_images halt with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · exact ⟨f, hm, ⟨hyc, hc, hd⟩⟩
  · let g : ParrottSylowSeedData n false :=
      { u := f.u
        w := f.w
        a := f.a*n.t
        b := f.b*n.v
        c := f.c*f.u
        d := f.d*f.w
        x := f.x
        derived_basis := f.derived_basis
        elementary_basis := Tits.ParrottSylowSeedRelations.residual_elementary_closure.trans
          f.elementary_basis
        core_generators := f.relations.residual_core_closure.trans f.core_generators
        sylow_generators := f.relations.residual_sylow_closure.trans f.sylow_generators
        relations := f.relations.residual_relations }
    have hgm : g.OuterMiddleRelations :=
      { eq16_ax := f.relations.residual_ax hm.eq16_ax
        comm_by := f.relations.residual_by hm.comm_by
        eq17_yd := f.relations.residual_yd hm.eq17_yd
        eq18_bx := f.relations.residual_bx hm.eq18_bx }
    exact ⟨g, hgm, ⟨f.relations.residual_yc hyc, hc, hd⟩⟩

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowSeedYdCoset: local-input version of the original construction. -/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- The initial commutator bound for a seed satisfying (16), in the global
recognition setting. The stronger local result `yd_cases` shows that neither
the global hypotheses nor (16) are needed for this bound. -/
public theorem yd_commutator_cases_of_local_inputs [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) (f : ParrottSylowSeedData n false)
    (_hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z)) :
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*z ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v*z :=
  f.yd_cases h hby

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowSeedBxNormalization: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] [Finite G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Normalize (18) without disturbing (16), (17), or any actual subgroup. -/
public theorem exists_outer_middle_relations_of_eq17_of_local_inputs [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (_hns : ¬ Group.IsSolvable G) (_hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z))
    (hyd : Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w) :
    ∃ f' : ParrottSylowSeedData n false, f'.OuterMiddleRelations := by
  rcases f.bx_eq_or_mul_z_of_eq17 h hax hby hyd with hb | hb
  · exact ⟨f, hax, hby, hyd, hb⟩
  · refine ⟨f.adjustXu, f.relations.adjust_xu_ax hax,
      f.relations.adjust_xu_by hby, f.relations.adjust_xu_eq17 hyd, ?_⟩
    have he := f.relations.adjust_xu_bx hb
      (f.relations.comm_au.symm.mul_right f.relations.comm_zu.symm)
      (f.relations.comm_az.symm.mul_right (Commute.refl z))
    simpa only [adjustXu, mul_assoc, ← pow_two, f.relations.z_sq, mul_one] using he

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowSeedMiddleNormalization: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Normalize equations (17)–(18) on the supplied actual local subgroups,
preserving (16) and using y=x²z for the resulting seed. -/
public theorem exists_outer_middle_relations_of_local_inputs [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z)) :
    ∃ f' : ParrottSylowSeedData n false, f'.OuterMiddleRelations := by
  exact f.exists_outer_middle_relations_of_eq17_normalization hax hby
    (yd_commutator_cases_of_local_inputs hns hlocal h f hax hby)
    (fun g hga hgb hgd => g.exists_outer_middle_relations_of_eq17_of_local_inputs hns hlocal h hga hgb hgd)

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowSeedOuterCentralization: local-input version of the original construction. -/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- The square of the supplied outer generator, multiplied by `z`,
centralizes the supplied seed element `b`. -/
public theorem b_comm_square_mul_z_of_local_inputs [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hlocal : ParrottLocalInputs z)
    (f : ParrottSylowSeedData n false) (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) :
    Commute f.b (f.x^2*z) := by
  have hz : z ≠ 1 := (orderOf_eq_prime_iff.mp h.involution).2
  obtain ⟨hb, hc, hd⟩ := f.outer_discrepancies_mem_derived h
  obtain ⟨⟨bi, bj, bk, hb⟩, ⟨ci, cj, ck, hc⟩, ⟨di, dj, dk, hd⟩⟩ :=
    Tits.ParrottSylowSeedRelations.outer_image_parameters f.relations hz hax hb hc hd
  exact Tits.ParrottSylowSeedRelations.b_comm_square_mul_z_of_parameters
    f.relations hz hax bi bj bk ci cj ck di dj dk hb hc hd

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowSeedOuterCompletion: local-input version of the original construction. -/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Reduce completion to the two remaining last-stage calculations. The second
input may change auxiliary coordinates; requiring the last relations on every
literal middle seed would contradict its proved residual symmetry. The actual
marked data and subgroup closures remain fixed by the seed type. -/
public theorem exists_generators_of_b_comm_square_mul_z_of_last_steps_of_local_inputs
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1)
    (hby : Commute f.b (f.x^2*z))
    (hyc_cases : ∀ g : ParrottSylowSeedData n false, g.OuterMiddleRelations →
      Tits.parrottCommutator (g.x^2*z) g.c = g.a*n.t ∨
        Tits.parrottCommutator (g.x^2*z) g.c = g.a*n.t*z)
    (hnormalize : ∀ g : ParrottSylowSeedData n false, g.OuterMiddleRelations →
      Tits.parrottCommutator (g.x^2*z) g.c = g.a*n.t*z →
      ∃ g' : ParrottSylowSeedData n false,
        g'.OuterMiddleRelations ∧ g'.OuterLastRelations) :
    Nonempty (ParrottSylowGeneratorData n) := by
  obtain ⟨g, hm⟩ := f.exists_outer_middle_relations_of_local_inputs hns hlocal h hax hby
  have hyc := g.eq19_yc_of_alternative_of_local_inputs hns hlocal h hm (hyc_cases g hm)
  obtain ⟨g', hm', hl'⟩ := hnormalize g hm hyc
  exact g'.generators_of_outer_relations hm' hl'

/-- Complete equations (16)–(19) from the initial seed centralization inputs.
All coordinate choices retain z,t,v,F and the supplied Sylow subgroup literally. -/
public theorem exists_generators_of_b_comm_square_mul_z_of_local_inputs
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1)
    (hby : Commute f.b (f.x^2*z)) :
    Nonempty (ParrottSylowGeneratorData n) := by
  apply f.exists_generators_of_b_comm_square_mul_z_of_last_steps_of_local_inputs hns hlocal h hax hby
  · exact fun g hm => g.yc_cases h hm
  · exact fun g hm hyc => exists_outer_last_normalization_of_local_inputs hns hlocal h g hm hyc

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowOuterNormalization: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- An unprimed Sylow seed extends to the full normalized Sylow frame.

The first outer normalization changes only the auxiliary `a,c` coordinates and
produces equation (16).  The centralization calculation then supplies the
hypothesis needed by the remaining coordinate changes, which complete
equations (17)--(19) while retaining the marked local data. -/
public theorem exists_generators_of_seed_of_local_inputs [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottSylowGeneratorData n) := by
  obtain ⟨g, hax⟩ := f.exists_ax_eq_one
  have hby := g.b_comm_square_mul_z_of_local_inputs hns hlocal h hax
  exact g.exists_generators_of_b_comm_square_mul_z_of_local_inputs hns hlocal h hax hby

end Stellmacher.Recognition.ParrottSylowSeedData

end

section

/- SylowGenerators: local-input version of the original construction. -/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable {z : G} {e : ParrottSecondElementaryData z}

/-- The supplied normalizer data admit normalized Sylow generators satisfying
the unprimed equations (1)–(19), with z,t,v and the actual E,F,J,T preserved. -/
public theorem ParrottNormalizerFusionData.exists_sylow_generators_of_local_inputs
    (n : ParrottNormalizerFusionData e) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottSylowGeneratorData n) := by
  obtain ⟨caseTwo, ⟨f⟩⟩ := n.exists_sylow_seed_of_local_inputs hns hlocal h
  exact f.normalize.exists_generators_of_seed_of_local_inputs hns hlocal h

end Stellmacher.Recognition

end
