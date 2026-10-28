module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Parabolic.Fixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.Normalization

/-!
# Normalization of the moving displacement by the selected two-residual

Fixing the selected class modulo B_c gives normalization of its Q_c
displacement by O²(P), using two-perfect commutator idempotence. This is
an assertion in the original vertex stabilizer and amalgam. Independently,
idempotence puts all residual commutators of B_c in U_c, since Z_c splits
as U_c and a central summand.

Source: MS93 (4.4.1)(1), printed pp.890–891. The generic normalization
argument is reused from FirstPairing/StepThree/RankOne/Normalization.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R} {f : FrameAt a c}

namespace FixedSeed
variable (s : FixedSeed geometry f)

/-- The supplied triple bound places the actual displacement in B_c. -/
theorem displacement_le_B (hb : 2 < geometry.b R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2) :
    ⁅zpowers s.element, Q R c⁆ ≤ B R c (geometry.Z_normal c) := by
  have hK : ⁅zpowers s.element, Q R c⁆ ≤ ⁅localZSpan R a c, Q R c⁆ :=
    commutator_mono (zpowers_le.mpr (Z_le_localZSpan R a c s.element_mem)) le_rfl
  intro x hx
  apply (mem_B_iff R c (geometry.Z_normal c)
    ((geometry.V_le_Q hb c hc).trans (fun _ hv => hv.1)) x).mpr
  refine ⟨(localZSpan_le_V R hd.le) (span_commutator_le_span a c (hK hx)), ?_⟩
  intro l hl
  apply f.triple_le_Z
  rw [commutator_comm]
  exact commutator_mem_commutator hl (hK hx)

/-- The actual two-residual normalizes the original displacement, before
any passage through the fixed-core quotient. -/
theorem displacement_normalized_twoResidual (source : LocalSource L R)
    (hb : 2 < geometry.b R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    (pResidual 2 (parabolic f.sectionData.projection s.flag s.side)).map
      (parabolic f.sectionData.projection s.flag s.side).subtype ≤
        normalizer ((⁅zpowers s.element, Q R c⁆).subgroupOf (stabilizer R c) :
          Set (stabilizer R c)) := by
  let S := stabilizer R c
  let Q₀ := (Q R c).subgroupOf S
  let B₀ := (B R c (geometry.Z_normal c)).subgroupOf S
  let Z₀ := (Z R c).subgroupOf S
  let P := parabolic f.sectionData.projection s.flag s.side
  let T := (pResidual 2 P).map P.subtype
  let := finite_stabilizer R c
  let := Q_normal R c
  let := fixed_normal (geometry := geometry) c
  have hQS : Q R c ≤ S := fun _ hx => hx.1
  have hxQ : s.element ∈ Q R c :=
    localZSpan_le_Q R hc hd.le hb (Z_le_localZSpan R a c s.element_mem)
  let x : S := ⟨s.element, hQS hxQ⟩
  have hA : (zpowers x).map S.subtype = zpowers s.element := MonoidHom.map_zpowers _ _
  have hK : ⁅zpowers x, Q₀⁆ = (⁅zpowers s.element, Q R c⁆).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_commutator, hA, map_subgroupOf_eq_of_le hQS,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans
        (sup_le ((zpowers_le.mpr hxQ).trans hQS) hQS))]
  rw [← hK]
  have hAT : ⁅zpowers x, T⁆ ≤ B₀ := by
    apply (commutator_mono le_rfl (map_subtype_le _)).trans
    apply map_le_iff_le_comap.mp
    rw [map_commutator, hA]
    exact s.class_fixed
  have hDT : ⁅B₀,T⁆ ≤ Z₀ := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro t ht b hb'
    have hbfix := ((mem_B_iff R c (geometry.Z_normal c)
      ((geometry.V_le_Q hb c hc).trans hQS) (b : FreeAmalgam R)).mp hb').2
    exact hbfix t (mem_map_of_mem S.subtype (map_pResidual_le 2 P.subtype ht))
  apply Escape.PairingControl.FirstPairing.StepThree.RankOne.pairing_normalized_of_radical_fixed
    (zpowers x) Q₀ B₀ Z₀ T
    (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
    (isPPerfect_embedded_pResidual 2 P) (zpowers_le.mpr hxQ) hAT hDT
  intro z hz q hq
  apply Subtype.ext
  exact commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc) hz q hq

/-- All global residual displacements of B_c lie in the actual U_c. -/
theorem B_residual_commutator_le_U (common : CommonFacts R source geometry)
    (hb : 2 < geometry.b R) (hc : color R c = false) :
    ⁅(B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c),
      pResidual 2 (stabilizer R c)⁆ ≤ (U R c).subgroupOf (stabilizer R c) := by
  let S := stabilizer R c
  let B₀ := (B R c (geometry.Z_normal c)).subgroupOf S
  let Z₀ := (Z R c).subgroupOf S
  let U₀ := (U R c).subgroupOf S
  let T := pResidual 2 S
  let := finite_stabilizer R c
  let := fixed_normal (geometry := geometry) c
  have hQS : Q R c ≤ S := fun _ hx => hx.1
  have hBZ : ⁅B₀,T⁆ ≤ Z₀ := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro t ht b hb'
    exact ((mem_B_iff R c (geometry.Z_normal c)
      ((geometry.V_le_Q hb c hc).trans hQS) (b : FreeAmalgam R)).mp hb').2 t
      (mem_map_of_mem S.subtype ht)
  have hZcomm : ⁅Z R c, S⁆ ≤ U R c := by
    have hsplit := (naturalStructure common).decomposition_at c hc
    have he := commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans hsplit.symm) inf_le_right
      ((U_le_Z R c).trans ((Z_le_stabilizer R c).trans S.le_normalizer))
    rw [commutator_comm, ← he]
    exact le_normalizer_iff_commutator_le_right.mp (U_normalized c)
  have hZU : ⁅Z₀,T⁆ ≤ U₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le (Z_le_stabilizer R c)]
    exact (commutator_mono le_rfl (map_subtype_le _)).trans hZcomm
  have hpB : IsPGroup 2 B₀ :=
    ((source.V_isPGroup geometry hb c hc).to_le
      (Escape.EdgeTransfer.B_le_radius hb c hc)).comap_subtype
  change ⁅B₀,T⁆ ≤ U₀
  rw [← commutator_isPPerfect_idempotent T B₀ (isPPerfect_pResidual 2) hpB
    le_normalizer_of_normal]
  exact (commutator_mono hBZ le_rfl).trans hZU

end FixedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
