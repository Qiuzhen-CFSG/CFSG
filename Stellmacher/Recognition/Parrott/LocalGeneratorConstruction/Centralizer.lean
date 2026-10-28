module

public import Stellmacher.Recognition.Parrott.CentralizerCompatibleClassification
public import Stellmacher.Recognition.Parrott.CentralizerElementarySelection
public import Stellmacher.Recognition.Parrott.CentralizerGenerators
public import Stellmacher.Recognition.Parrott.CentralizerInvolution
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.Geometry
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.LocalNormalizer.InvolutionCosets
public import Stellmacher.Recognition.Parrott.SecondNormalizerGrowthLocal
public import Stellmacher.Recognition.Parrott.SylowSquareTransport
public import Stellmacher.Recognition.Parrott.SylowYFusion

/-!
# Parrott generators from local inputs: Centralizer

The normalizer transport identifies the normalized y with the original
z-class. An outer centralizer involution with (ry)^5=1 is then selected and
its elementary action corrected by conjugations fixing y. Classifying and
normalizing its core action yields (20)–(23); the proved centralizer discrepancy
calculation gives (24), with the actual centralizer generation equality.

The derived-core normalizer identity and local normalizer solvability in
`ParrottLocalInputs` replace the ambient N₂ assumption. The original APIs
remain unchanged, and F, the supplied Sylow subgroup, t and v remain literal.

Source: D. Parrott, *A characterization of the Tits simple group* (1972),
§3, printed pp.678–682, with the local geometry of §§1–2.
-/

section

/- SylowSquareTransport: local-input version of the original construction. -/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowGeneratorData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- A normalizer conjugate of the supplied normalized x belongs to the
original two-core. No change of the normalized coordinates is made. -/
public theorem x_conjugate_mem_core_of_local_inputs (f : ParrottSylowGeneratorData n)
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
  have hxX : f.x ∈ X := by
    change f.x ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype
    rw [n.core_eq_sylow_centralizer]
    exact ⟨f.local_mem_sylow.2.2.2.2.2.2.2.2.2.1,
      mem_centralizer_singleton_iff.mpr
        ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)⟩
  have hxW : f.x ∉ W := by
    intro hx
    have hWC : W = X ⊓ centralizer
        ((center U).map ((N.subtype.comp K.subtype).comp U.subtype) : Set G) :=
      n.omega_eq_centralizer
    rw [hWC] at hx
    have hv : n.v ∈ (center U).map ((N.subtype.comp K.subtype).comp U.subtype) := by
      have hZ : (center U).map ((N.subtype.comp K.subtype).comp U.subtype) =
          (zpowers z ⊔ zpowers n.t) ⊔ zpowers n.v := n.omega_center_eq
      rw [hZ]
      exact mem_sup_right (mem_zpowers n.v)
    have hc : Commute f.x n.v := (mem_centralizer_iff.mp hx.2 n.v hv).symm
    have ht : n.t = 1 := f.eq01_xv.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ho := n.t_order
    rw [ht, orderOf_one] at ho
    norm_num at ho
  have hsqJ : f.x ^ 2 ∉ J.map H.subtype := by
    intro hx
    rw [f.eq04] at hx
    exact f.y_not_mem_core h
      ((J.map H.subtype).mul_mem_cancel_right (e.le_core e.z_mem_inf.2) |>.mp hx)
  have hsq2 : (f.x ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using f.eq01_x
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
end Stellmacher.Recognition.ParrottSylowGeneratorData

end

section

/- SylowYFusion: local-input version of the original construction. -/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The z-class meets the complement of the original two-core in C_G(z).
The original-core fusion theorem excludes the additional part of the core
from the conjugate supplied by fusion outside the derived subgroup. -/
public theorem ParrottNormalizerFusionData.exists_outer_isConj_z_of_local_inputs
    (n : ParrottNormalizerFusionData e) [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    ∃ u : G, u ∈ centralizer ({z} : Set G) ∧
      u ∉ (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype ∧ orderOf u = 2 ∧ IsConj z u := by
  obtain ⟨u, hu2, huH, huE, hzu⟩ := parrott_fusion_outside_derived_of_normalizer hns z h hlocal.derived_normalizer
  refine ⟨u, huH, ?_, hu2, hzu⟩
  intro huJ
  obtain ⟨l, hl⟩ := n.original_core_fusion u huJ huE hu2
  exact n.not_isConj (hzu.trans (isConj_iff.mpr ⟨(l : G), hl⟩).symm)

namespace ParrottSylowGeneratorData

variable (f : ParrottSylowGeneratorData n)

/-- Identifying yz with the second class forces the original normalized y
into the first class. The proof does not replace y by yz. -/
public theorem y_isConj_z_of_mul_z_isConj_v_of_local_inputs [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) (hyz : IsConj (f.y * z) n.v) :
    IsConj f.y z := by
  obtain ⟨u, huH, huJ, hu2, hzu⟩ := n.exists_outer_isConj_z_of_local_inputs hns hlocal h
  obtain ⟨a, ha⟩ := parrott_outer_involution_classes z h f.y u
    (e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.2.2.2.2.2.2)
    (f.y_not_mem_core h) (f.y_order h) huH huJ hu2
  rcases ha with ha | ha
  · exact (hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).symm
  · exact (n.not_isConj
      ((hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).trans hyz)).elim

/-- The class of the actual square in equation (4) suffices to identify y. -/
public theorem y_isConj_z_of_square_isConj_v_of_local_inputs [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) (hx : IsConj (f.x ^ 2) n.v) :
    IsConj f.y z := by
  exact f.y_isConj_z_of_mul_z_isConj_v_of_local_inputs hns hlocal h (f.eq04 ▸ hx)

/-- A normalizer transport of x into the original core and the class of
noncentral core squares complete the fusion argument on the supplied frame.
These are separate mathematical premises, not choices of new coordinates. -/
public theorem y_isConj_z_of_core_square_transport_of_local_inputs [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (htransport : ∃ q : normalizer (e.F : Set G),
      (q : G) * f.x * (q : G)⁻¹ ∈
        (pCore 2 (centralizer ({z} : Set G))).map
          (centralizer ({z} : Set G)).subtype)
    (hsquares : ∀ a : G,
      a ∈ (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype →
      a ^ 2 ∉ zpowers z → IsConj (a ^ 2) n.v) :
    IsConj f.y z := by
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let ZK := (center K).map (N.subtype.comp K.subtype)
  obtain ⟨q, hq⟩ := htransport
  let α := MulAut.conj (q : G)
  have hsq : (α f.x) ^ 2 ∉ zpowers z := by
    intro hs
    have hsZ : α (f.x ^ 2) ∈ ZK := by
      rw [map_pow]
      exact (zpowers_le.mpr e.z_mem_normalizer_core_center) hs
    have hxZ : f.x ^ 2 ∈ ZK :=
      (mem_normalizer_iff.mp (e.normalizer_core_centers_normalized.1 q.property)
        (f.x ^ 2)).mpr hsZ
    exact f.x_square_not_mem_core h (e.le_core (e.normalizer_core_center_le hxZ))
  have hv : IsConj ((α f.x) ^ 2) n.v := hsquares _ hq hsq
  apply f.y_isConj_z_of_square_isConj_v_of_local_inputs hns hlocal h
  have hc : IsConj (f.x ^ 2) ((α f.x) ^ 2) := by
    apply isConj_iff.mpr
    exact ⟨(q : G), (map_pow α f.x 2)⟩
  exact hc.trans hv

/-- The involution y in every complete normalized Sylow frame is conjugate
to the original z. The normalizer transports x itself into the original core,
whose noncentral squares belong to the class of v; equation (4) then fixes
the class of the supplied y without replacing any coordinate. -/
public theorem y_isConj_z_of_local_inputs [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) : IsConj f.y z := by
  exact f.y_isConj_z_of_core_square_transport_of_local_inputs hns hlocal h
    (f.x_conjugate_mem_core_of_local_inputs h hlocal) (f.core_square_isConj_v h)

end ParrottSylowGeneratorData
end Stellmacher.Recognition

end

section

/- CentralizerElementarySelection: local-input version of the original construction. -/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottSylowGeneratorData
variable (f : ParrottSylowGeneratorData n)

/-- Select an outer involution with the prescribed elementary action.  The
core-orientation theorem first chooses a seed whose action on the core
abelianization is oriented; duality transfers that action to the two
elementary generators modulo `⟨z⟩`; the central-factor correction then gives
the exact equations (20) and (21).  The supplied Sylow frame is retained
literally, so the witness is `f` itself. -/
public theorem exists_outer_involution_elementary_action_of_local_inputs
    (f : ParrottSylowGeneratorData n) [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    ∃ f' : ParrottSylowGeneratorData n, ∃ r : G,
      r ∈ centralizer ({z} : Set G) ∧ r ∉ e.sylow ∧ r ^ 2 = 1 ∧
      (r * f'.y) ^ 5 = 1 ∧
      r⁻¹ * n.t * r = f'.w * f'.u * n.v * z ∧
      r⁻¹ * n.v * r = f'.u * n.v := by
  obtain ⟨r, hrH, hrT, hr2, hry, hra, hrb, hrc, hrd⟩ :=
    f.exists_outer_involution_core_action h
  obtain ⟨htZ, hvZ⟩ :=
    f.t_v_conj_mod_center_of_core_action h r hrH hr2 hra hrb hrc hrd
  obtain ⟨r', hrH', hrT', hr2', hry', ht', hv'⟩ :=
    f.normalize_t_v_mod_center h r hrH hrT hr2 hry htZ hvZ
  exact ⟨f, r', hrH', hrT', hr2', hry', ht', hv'⟩

end ParrottSylowGeneratorData
end Stellmacher.Recognition

end

section

/- CentralizerInvolution: local-input version of the original construction. -/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Extend a complete normalized Sylow frame to an actual centralizer
involution satisfying equations (20)–(22). The supplied elementary subgroup
and normalizer-fusion data, hence F, T, z, t and v, are retained literally. -/
public theorem ParrottSylowGeneratorData.exists_centralizer_involution_of_local_inputs
    (f : ParrottSylowGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottCentralizerInvolutionData n) := by
  obtain ⟨f', r, hrH, hrT, hr2, hry, ht, hv⟩ :=
    f.exists_outer_involution_elementary_action_of_local_inputs hns hlocal h
  exact f'.centralizer_involution_of_t_v_conj h (f'.y_isConj_z_of_local_inputs hns hlocal h)
    r hrH hrT hr2 hry ht hv

end Stellmacher.Recognition

end

section

/- CentralizerCompatibleClassification: local-input version of the original construction. -/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The compatible action on the supplied frame has first parameter true
under the original finite nonsolvable simple hypotheses and local inputs. -/
public theorem ParrottCentralizerInvolutionData.exists_true_compatible_action_parameters_of_local_inputs
    [Finite G] [IsSimpleGroup G] (g : ParrottCentralizerInvolutionData n)
    (_hns : ¬ Group.IsSolvable G) (_hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    ∃ β δ γ : Bool, g.HasCompatibleActionParameters true β δ γ := by
  exact g.exists_true_compatible_action_parameters_of_exists h
    (g.exists_compatible_action_parameters h)

end Stellmacher.Recognition

end

section

/- CentralizerGenerators: local-input version of the original construction. -/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}

variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The original existence problem reduces solely to normalization of the
core action. The actual involution is constructed from the supplied frame. -/
public theorem ParrottSylowGeneratorData.exists_centralizer_generators_of_action_normalization_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottSylowGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (hnormalize : ∀ _g : ParrottCentralizerInvolutionData n,
      Nonempty (ParrottCentralizerActionData n)) :
    Nonempty (ParrottCentralizerGeneratorData n) := by
  obtain ⟨g⟩ := f.exists_centralizer_involution_of_local_inputs hns hlocal h
  obtain ⟨g'⟩ := hnormalize g
  exact ⟨g'.toGeneratorData h⟩

/-- Normalize the actual core action to the unprimed equations (23).
The second coset may change the Sylow coordinates, but retains e and n. -/
public theorem ParrottCentralizerInvolutionData.exists_normalized_action_of_local_inputs
    [Finite G] [IsSimpleGroup G] (g : ParrottCentralizerInvolutionData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottCentralizerActionData n) := by
  obtain ⟨β, δ, γ, hp⟩ := g.exists_true_compatible_action_parameters_of_local_inputs hns hlocal h
  obtain ⟨g', hp'⟩ := g.exists_compatible_action_parameters_normalized_signs β δ γ hp
  cases β with
  | false => exact ⟨g'.toActionDataOfCompatibleParameters hp'⟩
  | true => exact g'.nonempty_action_of_second_coset hp'

/-- Extend supplied normalized Sylow coordinates to generators of the actual
centralizer satisfying (20)–(24), including the unprimed equations (23).
The output may renormalize the Sylow coordinates while preserving e and n. -/
public theorem ParrottSylowGeneratorData.exists_centralizer_generators_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottSylowGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottCentralizerGeneratorData n) := by
  exact f.exists_centralizer_generators_of_action_normalization_of_local_inputs hns hlocal h
    (fun g => g.exists_normalized_action_of_local_inputs hns hlocal h)

end Stellmacher.Recognition

end
