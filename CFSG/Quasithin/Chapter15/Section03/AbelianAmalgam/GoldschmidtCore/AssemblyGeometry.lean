module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension

/-!
# The singular-line seed in the terminal Thompson argument

The residual of a singular-line stabilizer acts transitively on the three
nonidentity vectors of that line. The calculation uses the six graph lines
and the actual order-three rotations of the binary orthogonal four-space.
The compatible natural action lifts these conjugators to `Y_E`, proving
`E = ⟨Z^{Y_E}⟩` for every nontrivial subgroup `Z ≤ E`. Applied to the second
line, this supplies the seed used on p.1155 without an extra geometric premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the natural
action in 15.3.66 and the proof of 15.3.68, printed pp.1152–1155.
-/

public section

open Subgroup Stellmacher OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
open LocalRelations LocalRelations.OrthogonalProducts ThompsonExtension

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_line_orbit : ∀ i : LineCode, ∀ z w : Space,
    z ≠ 0 → w ≠ 0 → z.2 = planePermutation i z.1 →
    w.2 = planePermutation i w.1 → ∃ a : RotationCode,
      rotation a z = w ∧ ∀ v : Space,
        (rotation a v).2 = planePermutation i (rotation a v).1 ↔
          v.2 = planePermutation i v.1 := by decide +kernel

private theorem line_residual_orbit (E : Subgroup (Multiplicative Space))
    (hc : Nat.card E = 4) (hs : ∀ w ∈ E, form w.toAdd = 0)
    (z w : Multiplicative Space) (hz : z ≠ 1) (hw : w ≠ 1)
    (hzE : z ∈ E) (hwE : w ∈ E) :
    ∃ a ∈ lineResidual E, vectorAction a z = w := by
  obtain ⟨i, rfl⟩ := singular_four_eq_graph E hc hs
  obtain ⟨a, ha, hstab⟩ := finite_line_orbit i z.toAdd w.toAdd hz hw hzE hwE
  refine ⟨rotationHom a, ?_, ha⟩
  rw [lineResidual_eq_rotations_inter]
  exact ⟨⟨a, rfl⟩, hstab⟩

variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial subgroup of a singular four-group generates that line under its residual stabilizer. -/
theorem singular_line_eq_span (V M Y E Z : Subgroup G)
    (d : NaturalAction V M) (hYM : Y ≤ M) (hEV : E ≤ V)
    (hcard : Nat.card E = 4) (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hZ : Z ≠ ⊥) (hZE : Z ≤ E) : E = conjugateSpan (lineY Y E) Z := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hZ
    have hz' : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
    intro w hw
    by_cases hw' : w = 1
    · exact hw' ▸ (conjugateSpan (lineY Y E) Z).one_mem
    let zv : V := ⟨z, hEV (hZE z.property)⟩
    let wv : V := ⟨w, hEV hw⟩
    have hne (v : V) (hv : (v : G) ≠ 1) : d.coordinates v ≠ 1 := by
      intro h
      exact hv (congrArg Subtype.val (d.coordinates.injective (h.trans (map_one _).symm)))
    obtain ⟨a, ha, haw⟩ := line_residual_orbit (coordinateLine d E)
      ((coordinateLine_card d E hEV).trans hcard)
      (coordinateLine_singular d E hEV hs)
      (d.coordinates zv) (d.coordinates wv) (hne zv hz') (hne wv hw')
      ((mem_coordinateLine d E _).mpr (by simpa [zv] using hZE z.property))
      ((mem_coordinateLine d E _).mpr (by simpa [wv] using hw))
    rw [← actionImage_lineY d Y E hYM hEV himage] at ha
    obtain ⟨m, hm, rfl⟩ := ha
    have hconj : MulAut.conj (m : G) (z : G) = w := by
      rw [← d.intertwines m zv]
      change (d.coordinates.symm (vectorAction (d.action m) (d.coordinates zv)) : G) = w
      rw [haw, d.coordinates.symm_apply_apply]
    apply (le_iSup (fun y : lineY Y E => Z.map (MulAut.conj (y : G)⁻¹).toMonoidHom)
      ⟨(m : G)⁻¹, (lineY Y E).inv_mem hm⟩)
    exact mem_map.mpr ⟨z, z.property, by simpa using hconj⟩
  · apply iSup_le
    intro y
    exact (map_mono hZE).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((lineY_le Y E).trans inf_le_right
        ((lineY Y E).inv_mem y.property)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
