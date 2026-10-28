module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.OrbitChain
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechShortShellCounts
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechGenerators

/-!
# A two-orbit seed for a polynomial Leech cubic

For any Leech isometry, one of three coordinate differences on three distinct
coordinates has an image with even coordinates: the first two differences sum
to the third, and two odd lattice vectors sum to an even one. Choose this
minimal vector `x`. The cubic polynomial forces the raw dot product of `x`
and its image to be `-16`.

The even minimal-shell classification gives two cases for the image. For
shape `4²`, one nonzero coordinate lies outside the support of `x`; pair it
with a zero coordinate. For shape `2⁸`, use two nonzero coordinates outside
that support. Suitable signs produce a minimal vector `y` orthogonal to `x`
with raw dot product `16` against its image. Division by eight gives exactly
the integral pairings used by `CubicRootChain.ofNeighbor`.

This constructs the seed for the invariant E₈ argument associated with
Aschbacher, *Sporadic Groups* (1994), 25.1–25.9. It does not use the converse
of Chapter 9 Exercise 6 (p.141), which starts with an already selected cubic.
The coordinate membership, norms and even-shell classification are the
ATLAS results imported above, with attribution and licensing in those modules.
-/

open Atlas.Lattices Atlas.Codes
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness

@[expose] public noncomputable section

private theorem dot_sub (z u v : IntegerCoordinates) :
    integerDot z (u - v) = integerDot z u - integerDot z v := by
  simp [integerDot, mul_sub, Finset.sum_sub_distrib]

private theorem dot_neg (z u : IntegerCoordinates) :
    integerDot z (-u) = -integerDot z u := by
  simp [integerDot]

private theorem pair_neighbor (z : IntegerCoordinates) (a b c d : Omega)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d)
    (hz : z c + z d = 4 ∨ z c + z d = -4 ∨
      z c - z d = 4 ∨ z c - z d = -4) :
    ∃ y : IntegerCoordinates, y ∈ leech ∧ integerDot y y = 32 ∧
      y a = 0 ∧ y b = 0 ∧ integerDot z y = 16 := by
  have hp : (coordinateVector c 4 + coordinateVector d 4) a = 0 ∧
      (coordinateVector c 4 + coordinateVector d 4) b = 0 := by
    simp [coordinateVector, Ne.symm hca, Ne.symm hcb, Ne.symm hda, Ne.symm hdb]
  have hm : (coordinateVector c 4 - coordinateVector d 4) a = 0 ∧
      (coordinateVector c 4 - coordinateVector d 4) b = 0 := by
    simp [coordinateVector, Ne.symm hca, Ne.symm hcb, Ne.symm hda, Ne.symm hdb]
  have hneg (y : IntegerCoordinates) (hy : integerDot y y = 32) :
      integerDot (-y) (-y) = 32 := by simpa [integerDot] using hy
  rcases hz with h | h | h | h
  · refine ⟨_, coordinate_pair_mem c d, pair_norm c d hcd, hp.1, hp.2, ?_⟩
    rw [integerDot_add_right, integerDot_coordinateVector, integerDot_coordinateVector]
    omega
  · refine ⟨_, leech.neg_mem (coordinate_pair_mem c d), hneg _ (pair_norm c d hcd),
      by simpa only [Pi.neg_apply, neg_eq_zero] using hp.1,
      by simpa only [Pi.neg_apply, neg_eq_zero] using hp.2, ?_⟩
    rw [dot_neg, integerDot_add_right, integerDot_coordinateVector, integerDot_coordinateVector]
    omega
  · refine ⟨_, difference_mem c d, difference_norm c d hcd, hm.1, hm.2, ?_⟩
    rw [dot_sub, integerDot_coordinateVector, integerDot_coordinateVector]
    omega
  · refine ⟨_, leech.neg_mem (difference_mem c d), hneg _ (difference_norm c d hcd),
      by simpa only [Pi.neg_apply, neg_eq_zero] using hm.1,
      by simpa only [Pi.neg_apply, neg_eq_zero] using hm.2, ?_⟩
    rw [dot_neg, dot_sub, integerDot_coordinateVector, integerDot_coordinateVector]
    omega

private theorem even_neighbor (z : IntegerCoordinates) (hz : z ∈ leech)
    (hp : ∀ i, z i % 2 = 0) (hn : integerDot z z = 32)
    (a b : Omega) (hab : a ≠ b) (hdiff : z a - z b = -4) :
    ∃ y : IntegerCoordinates, y ∈ leech ∧ integerDot y y = 32 ∧
      y a = 0 ∧ y b = 0 ∧ integerDot z y = 16 := by
  classical
  have hcard : ({a,b} : Finset Omega).card = 2 := by simp [hab]
  rcases Finset.mem_union.mp ((even_minimal_shell_iff z).mp ⟨hz, hp, hn⟩) with h | h
  · have hs := twoFourFamily_shape 0 2 z h
    let S := evenMagnitudeSupport z 4
    have hS : S.card = 2 := hs.2.2
    have hsmall (i : Omega) : z i = -4 ∨ z i = 0 ∨ z i = 4 := by
      have hi : z i * z i ≠ 4 := by
        intro hi
        have hm : i ∈ evenMagnitudeSupport z 2 := by simp [evenMagnitudeSupport, hi]
        rw [Finset.card_eq_zero.mp hs.2.1] at hm
        exact Finset.notMem_empty _ hm
      rcases hs.1 i with hi' | hi' | hi' | hi' | hi' <;> simp_all
    have hnot : ¬ S ⊆ {a,b} := by
      intro hsub
      have he : S = {a,b} := Finset.eq_of_subset_of_card_le hsub (by omega)
      have ha : z a * z a = 4 * 4 := (Finset.mem_filter.mp (show a ∈ S by simp [he])).2
      have hb : z b * z b = 4 * 4 := (Finset.mem_filter.mp (show b ∈ S by simp [he])).2
      have ha' := mul_self_eq_mul_self_iff.mp ha
      have hb' := mul_self_eq_mul_self_iff.mp hb
      omega
    obtain ⟨c, hc, hc'⟩ := Finset.not_subset.mp hnot
    have hca : c ≠ a := by simpa using (fun he => hc' (by simp [he]))
    have hcb : c ≠ b := by simpa using (fun he => hc' (by simp [he]))
    have hbound : (S ∪ {a,b}).card < (Finset.univ : Finset Omega).card := by
      have hle := Finset.card_union_le S {a,b}
      have hu : (Finset.univ : Finset Omega).card = 24 := by decide
      omega
    obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hbound
    have hdS : d ∉ S := fun h => hd (Finset.mem_union_left _ h)
    have hda : d ≠ a := by intro he; apply hd; simp [he]
    have hdb : d ≠ b := by intro he; apply hd; simp [he]
    have hcd : c ≠ d := by intro he; exact hdS (he ▸ hc)
    have hdz : z d = 0 := by
      have hd' : z d * z d ≠ 16 := by simpa [S, evenMagnitudeSupport] using hdS
      rcases hsmall d with h | h | h <;> simp_all
    have hcz : z c = 4 ∨ z c = -4 :=
      mul_self_eq_mul_self_iff.mp (Finset.mem_filter.mp hc).2
    exact pair_neighbor z a b c d hca hcb hda hdb hcd (by omega)
  · have hs := twoFourFamily_shape 8 0 z h
    let S := evenMagnitudeSupport z 2
    have hS : S.card = 8 := hs.2.1
    have hlarge : 1 < (S \ {a,b}).card := by
      have hh := Finset.le_card_sdiff ({a,b} : Finset Omega) S
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hlarge
    obtain ⟨hcS, hc'⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hdS, hd'⟩ := Finset.mem_sdiff.mp hd
    have hca : c ≠ a := by intro he; apply hc'; simp [he]
    have hcb : c ≠ b := by intro he; apply hc'; simp [he]
    have hda : d ≠ a := by intro he; apply hd'; simp [he]
    have hdb : d ≠ b := by intro he; apply hd'; simp [he]
    have hcz : z c = 2 ∨ z c = -2 :=
      mul_self_eq_mul_self_iff.mp (Finset.mem_filter.mp hcS).2
    have hdz : z d = 2 ∨ z d = -2 :=
      mul_self_eq_mul_self_iff.mp (Finset.mem_filter.mp hdS).2
    exact pair_neighbor z a b c d hca hcb hda hdb hcd (by omega)


private def difference (a b : Omega) : leech :=
  ⟨coordinateVector a 4 - coordinateVector b 4, difference_mem a b⟩

private theorem exists_even_difference (r : LeechIsometryGroup) :
    ∃ a b : Omega, a ≠ b ∧ ∀ i, (r.val (difference a b)).val i % 2 = 0 := by
  let a : Omega := ((0,0),0)
  let b : Omega := ((0,0),1)
  let c : Omega := ((0,0),2)
  rcases leech_coordinate_parity _ (r.val (difference a b)).prop with h | h
  · exact ⟨a, b, by decide, h⟩
  rcases leech_coordinate_parity _ (r.val (difference b c)).prop with h' | h'
  · exact ⟨b, c, by decide, h'⟩
  refine ⟨a, c, by decide, ?_⟩
  have he : difference a c = difference a b + difference b c := by
    apply Subtype.ext
    change coordinateVector a 4 - coordinateVector c 4 =
      (coordinateVector a 4 - coordinateVector b 4) +
      (coordinateVector b 4 - coordinateVector c 4)
    abel
  intro i
  rw [he, map_add]
  change ((r.val (difference a b)).val i + (r.val (difference b c)).val i) % 2 = 0
  have h₁ := h i
  have h₂ := h' i
  omega

/-- A polynomial Leech cubic has the exact short-vector seed for two cubic orbits. -/
theorem cubicSeedExists : CubicSeedExists := by
  intro r _ hp
  obtain ⟨a, b, hab, heven⟩ := exists_even_difference r
  let x := difference a b
  have hx : integerDot x.val x.val = 32 := difference_norm a b hab
  have hz : integerDot (r.val x).val (r.val x).val = 32 := by
    rw [r.prop]
    exact hx
  have ho := cubic_orbit_pairing hp x
  have hangle : integerDot (r.val x).val x.val = -16 := by
    rw [integerDot_comm]
    omega
  change integerDot (r.val x).val (coordinateVector a 4 - coordinateVector b 4) = -16 at hangle
  rw [dot_sub, integerDot_coordinateVector, integerDot_coordinateVector] at hangle
  obtain ⟨y, hy, hyn, hya, hyb, hzy⟩ := even_neighbor (r.val x).val (r.val x).prop
    heven hz a b hab (by omega)
  have hxy : integerDot x.val y = 0 := by
    rw [integerDot_comm]
    change integerDot y (coordinateVector a 4 - coordinateVector b 4) = 0
    rw [dot_sub, integerDot_coordinateVector, integerDot_coordinateVector, hya, hyb]
    norm_num
  refine ⟨x, ⟨y, hy⟩, hx, hyn, ?_, ?_⟩
  · have h := leechIntegralPairing_mul x ⟨y, hy⟩
    change 8 * leechIntegralPairing x ⟨y, hy⟩ = integerDot x.val y at h
    rw [hxy] at h
    omega
  · have h := leechIntegralPairing_mul (r.val x) ⟨y, hy⟩
    change 8 * leechIntegralPairing (r.val x) ⟨y, hy⟩ = integerDot (r.val x).val y at h
    rw [hzy] at h
    omega

/-- The seed constructs the literal two-orbit chain used by the E₈ assembly. -/
theorem cubicRootChain_two_nonempty (r : LeechIsometryGroup) (hr : orderOf r = 3)
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) :
    Nonempty (CubicRootChain r 2) := by
  obtain ⟨x, y, hx, hy, hxy, hrxy⟩ := cubicSeedExists r hr hp
  exact ⟨CubicRootChain.ofNeighbor hp x y hx hy hxy hrxy⟩

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness
