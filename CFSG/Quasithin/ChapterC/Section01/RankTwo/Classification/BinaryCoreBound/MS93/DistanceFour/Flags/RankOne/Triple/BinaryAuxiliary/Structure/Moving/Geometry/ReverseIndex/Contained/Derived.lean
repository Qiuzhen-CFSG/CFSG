module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Pencils
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Transport
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
set_option maxHeartbeats 4000000
public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R}

private theorem base_matrixFixed_card (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    Nat.card (matrixFixed common.natural.marking source.flag i 1) = 4 := by
  have hZ := edge_commutator_le_edgeZ_of_early early (alpha R) (beta R) rfl (base_adjacent R)
  have hcard := early.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)
  have heq := Early.edge_fixed_natural_eq_commutator common (alpha R) (beta R) rfl
    (base_adjacent R) hZ hcard
  have hlocal : localFlagZ source i 1 = Z R (beta R) := by
    unfold localFlagZ localFlagKernel
    rw [localConjugate_one, hkernel]
    exact (Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)).symm
  let F := U R (alpha R) ⊓ Z R (beta R)
  have hFmap : (F.subgroupOf (U R (alpha R))).map common.natural.equiv.toMonoidHom =
      matrixFixed common.natural.marking source.flag i 1 := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      change common.natural.equiv u ∈
        matrixFixed common.natural.marking source.flag i 1
      have huLocal : (u : FreeAmalgam R) ∈ localFlagZ source i 1 := by
        rw [hlocal]
        exact hu.2
      simpa only [map_one] using
        (natural_mem_localFlagZ_iff source common.natural i 1 u).mp huLocal
    · intro hv
      obtain ⟨u, rfl⟩ := common.natural.equiv.surjective v
      change common.natural.equiv u ∈
        matrixFixed common.natural.marking source.flag i 1 at hv
      have huLocal : (u : FreeAmalgam R) ∈ localFlagZ source i 1 := by
        apply (natural_mem_localFlagZ_iff source common.natural i 1 u).mpr
        simpa only [map_one] using hv
      rw [hlocal] at huLocal
      exact ⟨u, ⟨u.property, huLocal⟩, rfl⟩
  rw [← hFmap, card_map_of_injective common.natural.equiv.injective,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, heq, hcard]


private theorem map_conj_map_local (A : Subgroup SL) (g : SL) (σ : MulAut SL) :
    (A.map (MulAut.conj g).toMonoidHom).map σ.toMonoidHom =
      (A.map σ.toMonoidHom).map (MulAut.conj (σ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

private theorem map_conj_one_local (A : Subgroup SL) :
    A.map (MulAut.conj (1 : SL)).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (1 : SL) * y * (1 : SL)⁻¹ ∈ A
    simpa using hy
  · intro hx
    exact ⟨x, hx, by simp⟩

private theorem conj_mul_map_local (A : Subgroup SL) (a b : SL) :
    A.map (MulAut.conj (a * b)).toMonoidHom =
      (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  apply congrArg (fun f : SL →* SL => A.map f)
  apply MonoidHom.ext
  intro x
  change (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹
  group

private theorem core_normalized_local (P : Subgroup SL) (g : SL) (hg : g ∈ P) :
    (P.pCoreIn 2).map (MulAut.conj g).toMonoidHom = P.pCoreIn 2 := by
  exact mem_normalizer_iff_map_conj_eq.mp
    ((P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))) hg)

private theorem hplane_of_line (l : SL) (hl : l ∈ lineParabolicSL) :
    pointLine.map (vectorAction l).toMonoidHom ≤ incidentPlane := by
  have hnorm : BinaryLinearThree.R.map (MulAut.conj l).toMonoidHom =
      BinaryLinearThree.R := by
    rw [← Matrix.PSL3Two.lineParabolicSL_pCoreIn_two_eq_R]
    exact core_normalized_local lineParabolicSL l hl
  have hfixed : incidentPlane.map (vectorAction l).toMonoidHom = incidentPlane := by
    rw [← fixed_lineCore, ← fixedSpace_conj, hnorm]
  rw [← hfixed]
  exact map_mono line_le_plane

private theorem matrix_fixed_incident_le_base (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    matrixFixed common.natural.marking source.flag (!i) (source.projection d) ≤
      matrixFixed common.natural.marking source.flag i 1 := by
  have hcard := base_matrixFixed_card common early i hkernel
  obtain ⟨k, hp | hp⟩ := marked_pair common.natural.marking source.flag i
  · have hbase : matrixFixed common.natural.marking source.flag i 1 =
        pointLine.map (vectorAction k).toMonoidHom := by
      unfold matrixFixed matrixCore
      rw [map_conj_one_local]
      rw [map_pCoreIn_of_injective 2 _ _ common.natural.marking.injective,
        show (modelParabolic source.flag i).map common.natural.marking.toMonoidHom =
          markedParabolic common.natural.marking source.flag i from rfl,
        hp.1, core_fixed_conj, MarkedProduct.pointParabolic_core, fixed_pointCore]
    have hc : Nat.card (matrixFixed common.natural.marking source.flag i 1) =
        Nat.card (pointLine.map (vectorAction k).toMonoidHom) :=
      congrArg (fun H : Subgroup VectorGroup => Nat.card H) hbase
    rw [hc, Subgroup.card_map_of_injective (f := (vectorAction k).toMonoidHom)
      (vectorAction k).injective, line_card] at hcard
    omega
  · have hbase : matrixFixed common.natural.marking source.flag i 1 =
        incidentPlane.map (vectorAction k).toMonoidHom := by
      unfold matrixFixed matrixCore
      rw [map_conj_one_local]
      rw [map_pCoreIn_of_injective 2 _ _ common.natural.marking.injective,
        show (modelParabolic source.flag i).map common.natural.marking.toMonoidHom =
          markedParabolic common.natural.marking source.flag i from rfl,
        hp.1, core_fixed_conj, lineParabolicSL_pCoreIn_two_eq_R, fixed_lineCore]
    obtain ⟨m, hm, hm'⟩ := (flagIncident_one_iff source i d).mp hd
    have hmP : source.projection m ∈ modelParabolic source.flag i := by
      change source.projection m ∈ modelParabolic source.flag i at hm
      exact hm
    have hq : source.projection d⁻¹ * source.projection m ∈
        modelParabolic source.flag (!i) := by
      change source.projection (d⁻¹ * m) ∈ modelParabolic source.flag (!i) at hm'
      simpa only [map_mul, map_inv] using hm'
    have hg : source.projection d =
        source.projection m * (source.projection d⁻¹ * source.projection m)⁻¹ := by
      have hh : d = m * (d⁻¹ * m)⁻¹ := by group
      simpa only [map_mul, map_inv] using congrArg source.projection hh
    have hcore :
        matrixCore source.flag (!i) (source.projection d) =
          ((modelParabolic source.flag (!i)).pCoreIn 2).map
            (MulAut.conj (source.projection m)).toMonoidHom := by
      unfold matrixCore
      rw [hg, conj_mul_map_local]
      rw [core_normalized_local (modelParabolic source.flag (!i))
        (source.projection d⁻¹ * source.projection m)⁻¹
        ((modelParabolic source.flag (!i)).inv_mem hq)]
    have hfix :
        matrixFixed common.natural.marking source.flag (!i) (source.projection d) =
          (pointLine.map (vectorAction k).toMonoidHom).map
            (vectorAction (common.natural.marking (source.projection m))).toMonoidHom := by
      unfold matrixFixed
      rw [hcore, map_conj_map_local,
        map_pCoreIn_of_injective 2 _ _ common.natural.marking.injective,
        show (modelParabolic source.flag (!i)).map common.natural.marking.toMonoidHom =
          markedParabolic common.natural.marking source.flag (!i) from rfl]
      rw [hp.2, fixedSpace_conj, core_fixed_conj, MarkedProduct.pointParabolic_core, fixed_pointCore]
    rw [hfix]
    have hmarked : common.natural.marking (source.projection m) ∈
        markedParabolic common.natural.marking source.flag i :=
      mem_map_of_mem common.natural.marking.toMonoidHom hmP
    rw [hp.1] at hmarked
    obtain ⟨l, hl, heq⟩ := hmarked
    rw [← heq]
    change (pointLine.map (vectorAction k).toMonoidHom).map
        (vectorAction (MulAut.conj k l)).toMonoidHom ≤
      matrixFixed common.natural.marking source.flag i 1
    rw [map_action_conj]
    exact (map_mono (hplane_of_line l hl)).trans_eq hbase.symm


private theorem localFlagZ_opposite_le_edgeZ (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    localFlagZ source (!i) d ≤ Z R (beta R) := by
  let structureData : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have hs := structureData.decomposition_at (alpha R) rfl
  let F := Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))
  have hFU : F ≤ normalizer (U R (alpha R)) :=
    (inf_le_left.trans (Z_le_stabilizer R _)).trans (U_normalized _)
  have hF : F ≤ Z R (beta R) := by
    rw [Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]
    refine le_inf inf_le_left ?_
    exact inf_le_right.trans (centralizer_le
      (show (Q R (beta R) : Set (FreeAmalgam R)) ⊆
        (stabilizer R (alpha R) : Set (FreeAmalgam R)) from
      fun _ hx => hx.2 (alpha R) (adjacent_symm R (base_adjacent R))))
  intro x hx
  have hprod : x ∈ (U R (alpha R) : Set (FreeAmalgam R)) * (F : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hFU, ← hs]
    exact hx.1
  obtain ⟨u, hu, f, hf, rfl⟩ := hprod
  have hfK : f ∈ centralizer (localFlagKernel source (!i) d : Set (FreeAmalgam R)) :=
    (centralizer_le (show (localFlagKernel source (!i) d : Set (FreeAmalgam R)) ⊆
      (stabilizer R (alpha R) : Set (FreeAmalgam R)) from
      fun _ hy => localFlagKernel_le_stabilizer source (!i) d hy)) hf.2
  have huK : u ∈ centralizer (localFlagKernel source (!i) d : Set (FreeAmalgam R)) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (localFlagKernel source (!i) d : Set (FreeAmalgam R))).mul_mem hx.2
        ((centralizer (localFlagKernel source (!i) d : Set (FreeAmalgam R))).inv_mem hfK)
  have huLocal : u ∈ localFlagZ source (!i) d :=
    ⟨(U_le_Z (alpha R)) hu, huK⟩
  have hmatOpp := (natural_mem_localFlagZ_iff source common.natural (!i) d
      ⟨u, hu⟩).mp huLocal
  have hmatBase := matrix_fixed_incident_le_base common early i hkernel d hd hmatOpp
  have huBase : u ∈ localFlagZ source i 1 := by
    apply (natural_mem_localFlagZ_iff source common.natural i 1 ⟨u, hu⟩).mpr
    simpa only [map_one] using hmatBase
  have huZ : u ∈ Z R (beta R) := by
    rw [show localFlagZ source i 1 = Z R (beta R) by
      unfold localFlagZ localFlagKernel
      rw [localConjugate_one, hkernel]
      exact (Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)).symm] at huBase
    exact huBase
  exact (Z R (beta R)).mul_mem huZ (hF hf)
/-- The derived subgroup of an incident second layer lies in the edge center. -/
theorem secondFlagLayer_derived_le_edge_Z (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    ⁅secondFlagLayer source i d, secondFlagLayer source i d⁆ ≤ Z R (beta R) := by
  exact (commutator_mono (second_le_Y source i d) (second_le_Y source i d)).trans
    ((Y_commutator_le_localZ source geometry common early i hkernel d).trans
      (localFlagZ_opposite_le_edgeZ common early i hkernel d hd))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
