module

public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed
public import Stellmacher.Recognition.Parrott.FusionOutsideDerived
public import Stellmacher.Recognition.Parrott.OuterInvolutionClasses
public import Stellmacher.Recognition.Parrott.CoreSquareFusion
public import Stellmacher.Recognition.Parrott.SylowSquareTransport

/-!
# The global class of the normalized Sylow involution

The earlier choice of an outer involution in the class of z cannot simply be
carried through the normalization of the Sylow generators. For the supplied
normalized frame, equation (4) instead reduces the question to the class of
x² = yz. If this square is conjugate to v, the two-representative cover in
H = C_G(z) forces y to be conjugate to z: fusion outside the derived core
supplies a z-conjugate outside O₂(H), and it cannot belong to the yz class.

The final theorem discharges both local calculations using SylowSquareTransport
and CoreSquareFusion: transport x by N_G(F) into O₂(H), then identify its
noncentral square with the class of v. The transported square cannot lie in
⟨z⟩, since N_G(F) preserves the center of its two-core, which lies in O₂(H),
whereas x² does not. Every supplied coordinate is retained.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.677–680, especially the deduction of equation (4) on p.678.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The z-class meets the complement of the original two-core in C_G(z).
The original-core fusion theorem excludes the additional part of the core
from the conjugate supplied by fusion outside the derived subgroup. -/
public theorem ParrottNormalizerFusionData.exists_outer_isConj_z
    (n : ParrottNormalizerFusionData e) [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ u : G, u ∈ centralizer ({z} : Set G) ∧
      u ∉ (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype ∧ orderOf u = 2 ∧ IsConj z u := by
  obtain ⟨u, hu2, huH, huE, hzu⟩ := parrott_fusion_outside_derived hns hN z h
  refine ⟨u, huH, ?_, hu2, hzu⟩
  intro huJ
  obtain ⟨l, hl⟩ := n.original_core_fusion u huJ huE hu2
  exact n.not_isConj (hzu.trans (isConj_iff.mpr ⟨(l : G), hl⟩).symm)

namespace ParrottSylowGeneratorData

variable (f : ParrottSylowGeneratorData n)

/-- The normalized fourth-order generator belongs to the actual normalizer
two-core, because it belongs to T and centralizes t. -/
public theorem x_mem_normalizer_core :
    f.x ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype := by
  rw [n.core_eq_sylow_centralizer]
  exact ⟨f.local_mem_sylow.2.2.2.2.2.2.2.2.2.1,
    mem_centralizer_singleton_iff.mpr
      ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)⟩

/-- Equation (4) places the square of x outside the original two-core. -/
public theorem x_square_not_mem_core [Finite G]
    (h : ParrottCentralizerHypotheses z) :
    f.x ^ 2 ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
  intro hx
  rw [f.eq04] at hx
  exact f.y_not_mem_core h
    (((pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype).mul_mem_cancel_right
        (e.le_core e.z_mem_inf.2) |>.mp hx)

/-- Identifying yz with the second class forces the original normalized y
into the first class. The proof does not replace y by yz. -/
public theorem y_isConj_z_of_mul_z_isConj_v [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) (hyz : IsConj (f.y * z) n.v) :
    IsConj f.y z := by
  obtain ⟨u, huH, huJ, hu2, hzu⟩ := n.exists_outer_isConj_z hns hN h
  obtain ⟨a, ha⟩ := parrott_outer_involution_classes z h f.y u
    (e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.2.2.2.2.2.2)
    (f.y_not_mem_core h) (f.y_order h) huH huJ hu2
  rcases ha with ha | ha
  · exact (hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).symm
  · exact (n.not_isConj
      ((hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).trans hyz)).elim

/-- The class of the actual square in equation (4) suffices to identify y. -/
public theorem y_isConj_z_of_square_isConj_v [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) (hx : IsConj (f.x ^ 2) n.v) :
    IsConj f.y z := by
  exact f.y_isConj_z_of_mul_z_isConj_v hns hN h (f.eq04 ▸ hx)

/-- A normalizer transport of x into the original core and the class of
noncentral core squares complete the fusion argument on the supplied frame.
These are separate mathematical premises, not choices of new coordinates. -/
public theorem y_isConj_z_of_core_square_transport [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
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
  apply f.y_isConj_z_of_square_isConj_v hns hN h
  have hc : IsConj (f.x ^ 2) ((α f.x) ^ 2) := by
    apply isConj_iff.mpr
    exact ⟨(q : G), (map_pow α f.x 2)⟩
  exact hc.trans hv

/-- The involution y in every complete normalized Sylow frame is conjugate
to the original z. The normalizer transports x itself into the original core,
whose noncentral squares belong to the class of v; equation (4) then fixes
the class of the supplied y without replacing any coordinate. -/
public theorem y_isConj_z [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) : IsConj f.y z := by
  exact f.y_isConj_z_of_core_square_transport hns hN h
    (f.x_conjugate_mem_core h hN) (f.core_square_isConj_v h)

end ParrottSylowGeneratorData
end Stellmacher.Recognition
