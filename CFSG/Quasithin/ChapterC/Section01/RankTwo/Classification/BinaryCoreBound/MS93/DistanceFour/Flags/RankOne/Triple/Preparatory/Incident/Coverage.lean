module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs

/-!
# Selecting the incident core crossed by the critical endpoint

The four elements of either binary parabolic core lie in the three incident
opposite cores. Small explicit matrix calculations prove this at the standard
flag; conjugation transports it to the supplied flag. The two-group kernel
then lifts the core coverage through the original marked quotient.

`exists_delta2` applies this coverage to the critical endpoint, using its
containment in Q_beta and its escape from Q_alpha. All subgroups are embedded
by the original amalgam map. This is the selection before claim (3), not a
proof of either numbered claim (3) or (4).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the local flag choice on printed p.905 and its use on p.906.
-/

public section
open Subgroup Matrix
open Matrix.PSL3Two
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident

private def pointShear (a b : ZMod 2) : SL :=
  ⟨!![1,a,b; 0,1,0; 0,0,1], by simp [det_fin_three]⟩
private def swapLast : SL := ⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩
private def addLast : SL := ⟨!![1,0,0; 0,1,0; 0,1,1], by decide⟩
private def swapFirst : SL := ⟨!![0,1,0; 1,0,0; 0,0,1], by decide⟩
private def addFirst : SL := ⟨!![1,0,0; 1,1,0; 0,0,1], by decide⟩

private theorem pointShear_cover (a b : ZMod 2) :
    ∃ c ∈ pointParabolicSL,
      c⁻¹ * pointShear a b * c ∈ lineParabolicSL.pCoreIn 2 := by
  rw [lineParabolicSL_pCoreIn_two_eq_R]
  fin_cases a <;> fin_cases b
  · exact ⟨1, one_mem _, Multiplicative.ofAdd (0, 0), by decide⟩
  · exact ⟨1, one_mem _, Multiplicative.ofAdd (1, 0), by decide⟩
  · exact ⟨swapLast, by decide, Multiplicative.ofAdd (1, 0), by decide⟩
  · exact ⟨addLast, by decide, Multiplicative.ofAdd (1, 0), by decide⟩

private theorem point_core_cover (x : SL) (hx : x ∈ pointParabolicSL.pCoreIn 2) :
    ∃ c ∈ pointParabolicSL, c⁻¹ * x * c ∈ lineParabolicSL.pCoreIn 2 := by
  rw [MarkedProduct.pointParabolic_core] at hx
  obtain ⟨h00, h10, h20, h11, h12, h21, h22⟩ := hx
  have he : x = pointShear (x.val 0 1) (x.val 0 2) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pointShear, h00, h10, h20, h11, h12, h21, h22]
  rw [he]
  exact pointShear_cover _ _

private theorem line_core_cover (x : SL) (hx : x ∈ lineParabolicSL.pCoreIn 2) :
    ∃ c ∈ lineParabolicSL, c⁻¹ * x * c ∈ pointParabolicSL.pCoreIn 2 := by
  rw [lineParabolicSL_pCoreIn_two_eq_R] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  rw [MarkedProduct.pointParabolic_core]
  fin_cases a <;> fin_cases b
  · exact ⟨1, one_mem _, by decide⟩
  · exact ⟨swapFirst, by decide, by decide⟩
  · exact ⟨1, one_mem _, by decide⟩
  · exact ⟨addFirst, by decide, by decide⟩

/-- Every element of a binary parabolic core belongs to an incident opposite core.
The conjugator lies in the first parabolic, retaining the common quotient marking. -/
theorem model_core_cover (g : SL) (i : Bool) (x : SL)
    (hx : x ∈ (modelParabolic g i).pCoreIn 2) :
    ∃ c ∈ modelParabolic g i, c⁻¹ * x * c ∈ (modelParabolic g (!i)).pCoreIn 2 := by
  let e := MulAut.conj g
  let P := if i then lineParabolicSL else pointParabolicSL
  let S := if !i then lineParabolicSL else pointParabolicSL
  have hx' : x ∈ (P.pCoreIn 2).map e.toMonoidHom := by
    rw [map_pCoreIn_of_injective 2 P e.toMonoidHom e.injective]
    exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have hcover : ∃ c ∈ P, c⁻¹ * y * c ∈ S.pCoreIn 2 := by
    cases i
    · exact point_core_cover y hy
    · exact line_core_cover y hy
  obtain ⟨c, hc, hcy⟩ := hcover
  refine ⟨e c, mem_map_of_mem _ hc, ?_⟩
  change _ ∈ (S.map e.toMonoidHom).pCoreIn 2
  rw [← map_pCoreIn_of_injective 2 S e.toMonoidHom e.injective]
  exact ⟨c⁻¹ * y * c, hcy, by simp only [map_mul, map_inv]; rfl⟩

open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The intrinsic core of a marked parabolic is the full preimage of its model core. -/
theorem parabolic_core_eq_comap (source : LocalSource L R) (i : Bool) :
    (parabolic source.projection source.flag i).pCoreIn 2 =
      ((modelParabolic source.flag i).pCoreIn 2).comap source.projection := by
  let P := parabolic source.projection source.flag i
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  have hkP : source.projection.ker ≤ P := by
    intro x hx
    change source.projection x ∈ modelParabolic source.flag i
    rw [show source.projection x = 1 from hx]
    exact one_mem _
  have hkcore : source.projection.ker ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hk hkP le_normalizer_of_normal
  have hm := map_pCoreIn_of_ker_isPGroup source.projection hk P
  have hp : P.map source.projection = modelParabolic source.flag i :=
    map_comap_eq_self_of_surjective source.projection_surjective _
  rw [hp] at hm
  have h := congrArg (Subgroup.comap source.projection) hm
  rw [comap_map_eq_self hkcore] at h
  exact h

/-- The incident opposite cores cover the first core through the original embedding. -/
theorem flagKernel_covered (source : LocalSource L R) (i : Bool)
    (x : FreeAmalgam R) (hx : x ∈ flagKernel source i) :
    ∃ d : M, flagIncident source i 1 d ∧ x ∈ localFlagKernel source (!i) d := by
  change x ∈ ((parabolic source.projection source.flag i).pCoreIn 2).map (embedM R) at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [parabolic_core_eq_comap source i] at hy
  obtain ⟨c, hc, hcy⟩ := model_core_cover source.flag i (source.projection y) hy
  obtain ⟨d, rfl⟩ := source.projection_surjective c
  have hd : d ∈ parabolic source.projection source.flag i := hc
  have hyd : d⁻¹ * y * d ∈ (parabolic source.projection source.flag (!i)).pCoreIn 2 := by
    rw [parabolic_core_eq_comap source (!i)]
    change source.projection (d⁻¹ * y * d) ∈ (modelParabolic source.flag (!i)).pCoreIn 2
    simpa only [map_mul, map_inv] using hcy
  refine ⟨d, ⟨d, by simpa only [inv_one, one_mul] using hd,
    by simp only [inv_mul_cancel]; exact one_mem _⟩, ?_⟩
  refine ⟨embedM R (d⁻¹ * y * d), mem_map_of_mem (embedM R) hyd, ?_⟩
  change embedM R d * embedM R (d⁻¹ * y * d) * (embedM R d)⁻¹ = embedM R y
  simp only [map_mul, map_inv]
  group

/-- Any subgroup of the first core escaping Q_alpha crosses an incident opposite core. -/
theorem exists_incident_crossing (source : LocalSource L R) (i : Bool)
    (H : Subgroup (FreeAmalgam R)) (hH : H ≤ flagKernel source i)
    (hnot : ¬ H ≤ Q R (alpha R)) :
    ∃ d : M, flagIncident source i 1 d ∧
      ¬ H ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) := by
  classical
  obtain ⟨x, hx, hxQ⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨d, hd, hxd⟩ := flagKernel_covered source i x (hH hx)
  exact ⟨d, hd, fun h => hxQ (h ⟨hx, hxd⟩)⟩

/-- The literal delta2 selection preceding claim (3), with the critical endpoint. -/
theorem exists_delta2 (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i) :
    ∃ d : M, flagIncident source i 1 d ∧
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) :=
  exists_incident_crossing source i (Z R p.endpoint)
    ((p.endpoint_le_edgeKernel hb).trans_eq hkernel.symm) (p.endpoint_not_le_Q common)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
