module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.HighestRoot
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.LeviAction

/-!
# Placement and Levi centralization of the triality unipotent center

A central unipotent element commutes with the fixed central-simple curve at
parameter one. A Geck matrix entry therefore kills the first arm coordinate,
and graph-field fixedness kills the remaining two arm coordinates. Faithful
positive coordinates and the injective characteristic-two central quotient
put the embedded center in the descended arms radical, including at q = 2.
Independently, both signs of the arm-simple curves commute with the highest
root. Closure and the actual descent therefore put the arms Levi subgroup
in the centralizer of the highest-root subgroup. Identifying the radical's
center with that subgroup is a separate commutator calculation.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, printed pp.262–264).
-/

@[expose] public section

open Triality.Standard.PositiveCoordinates
namespace Triality.Standard.RadicalCoordinates.Centers
open Parabolics
noncomputable section

lemma fixed_positive_commutant_le_arms (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hg : g ∈ positiveSubgroup P)
    (hfix : graphFieldAutomorphism P g = g) (hc : Commute g (curve P 3 1)) :
    g ∈ rootSubgroup P .arms := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  obtain ⟨v, rfl⟩ := (show g ∈ Set.range (orderedProduct (binaryParameters n hn)) by
    rw [range_orderedProduct_binary]; exact hg)
  have hv := (orderedProduct_mem_fixedSubgroup_iff_binary n hn v).mp hfix
  have h0 := UnipotentMatrices.first_coordinate_zero _ rfl v hc
  have h1 : v 1 = 0 := by simpa only [show diagram 0 = 1 from rfl, h0, map_zero] using hv 0
  have h2 : v 2 = 0 := by simpa only [show diagram 1 = 2 from rfl, h1, map_zero] using hv 1
  apply orderedProduct_mem_rootSubgroup _ .arms ⟨v, ?_⟩
  intro i hi
  have hi' : i.val < 3 := by simpa only [rootSupport, not_le] using hi
  fin_cases i <;> first | exact h0 | exact h1 | exact h2 | norm_num at hi'

theorem center_unipotent_le_descendedRootSubgroup (P : Parameters) (hp : P.prime = 2) :
    (Subgroup.center (unipotent P)).map (unipotent P).subtype ≤
      descendSubgroup P (rootSubgroup P .arms) := by
  rintro z ⟨z, hz, rfl⟩
  obtain ⟨e, he, hez⟩ := z.property
  let c := ElementaryCentralKernel.centralElementary P true 1 (map_one _)
  have hc : toCarrier P c ∈ unipotent P :=
    ⟨c, positiveRoot_mem_positiveSubgroup P 1 1, rfl⟩
  have hzc : Commute z (⟨toCarrier P c, hc⟩ : unipotent P) :=
    ((Subgroup.mem_center_iff.mp hz) _).symm
  have hmap : Commute (toCarrier P e) (toCarrier P c) :=
    (congrArg (fun w : Carrier P => Commute w (toCarrier P c)) hez).mpr
      (hzc.map (unipotent P).subtype)
  have hec : Commute e c :=
    Commute.of_map (ElementaryCentralKernel.toCarrier_injective P hp) hmap
  refine ⟨e, fixed_positive_commutant_le_arms P hp (elementaryInclusion P e)
    he e.val.property ?_, hez⟩
  have hh := hec.map (elementaryInclusion P)
  change Commute (elementaryInclusion P e) (positiveRoot P 1 1) at hh
  simpa only [show (3 : Fin 12) = simplePosition 1 from rfl, curve_simple] using hh

private theorem splitLevi_le_centralizer_splitHighestRoot (P : Parameters)
    (hp : P.prime = 2) :
    splitLevi P .arms ≤ Subgroup.centralizer (splitHighestRoot P : Set (SplitGroup P)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, hi, t, rfl | rfl⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    rintro z ⟨s, rfl⟩
    change curve P 11 s.toAdd * positiveRoot P i t =
      positiveRoot P i t * curve P 11 s.toAdd
    simpa only [curve_simple] using (highestCurve_commute P (simplePosition i) s.toAdd t).eq
  · apply Subgroup.mem_centralizer_iff.mpr
    rintro z ⟨s, rfl⟩
    exact (UnipotentLevi.highestCurve_commute_negativeRoot P hp i hi s.toAdd t).eq

/-- The descended arms subsystem centralizes the actual highest-root subgroup.
Both signed generating curves have been checked on the full Geck lattice. -/
theorem levi_le_centralizer_highestRoot (P : Parameters) (hp : P.prime = 2) :
    levi P .arms ≤ Subgroup.centralizer (highestRoot P : Set (Carrier P)) := by
  rintro x ⟨e, he, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨d, hd, rfl⟩
  have hc : Commute (elementaryInclusion P d) (elementaryInclusion P e) :=
    Subgroup.mem_centralizer_iff.mp
      (splitLevi_le_centralizer_splitHighestRoot P hp he) _ hd
  have hde : Commute d e :=
    Commute.of_map (fun _ _ h => Subtype.ext (Subtype.ext h)) hc
  exact (hde.map (toCarrier P)).eq

end
end Triality.Standard.RadicalCoordinates.Centers
