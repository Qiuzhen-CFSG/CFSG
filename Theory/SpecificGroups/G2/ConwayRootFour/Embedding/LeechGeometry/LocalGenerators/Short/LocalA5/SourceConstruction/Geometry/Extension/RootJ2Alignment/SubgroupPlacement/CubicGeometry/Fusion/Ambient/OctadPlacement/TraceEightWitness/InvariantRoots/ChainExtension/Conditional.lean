module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.Geometry

/-!
# Transport of the two chain-extension steps

The first two cubic orbits form a marked D₄ configuration. A coordinate
placement gives the first extension explicitly. The second extension uses
only the normalized six-vector configuration; its witness is pulled back
by the same Leech isometry. The polynomial identity supplies the reverse
mixed pairings, so the local completion theorem need not refer to a cubic.

This is a conditional assembly. The two geometric obligations in `Geometry`
remain unproved here; no universal extension theorem is asserted.

Source context: Aschbacher, *Sporadic Groups* (1994), 22.13 and 25.1–25.5.
The reduction to the two displayed coordinate obligations is proved here,
not attributed to the converse of Chapter 9 Exercise 6.
-/

open Atlas.Lattices Atlas.Codes
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness

@[expose] public noncomputable section

namespace ChainExtension

theorem pairing_map (g : LeechIsometryGroup) (x y : leech) :
    leechIntegralPairing (g.val x) (g.val y) = leechIntegralPairing x y := by
  unfold leechIntegralPairing
  rw [g.prop]

theorem orbit_cross_sum {r : LeechIsometryGroup}
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) (x y : leech) :
    leechIntegralPairing (r.val x) y + leechIntegralPairing x y +
      leechIntegralPairing x (r.val y) = 0 := by
  have h := congrArg (fun z : leech => leechIntegralPairing z (r.val y)) (hp x)
  simpa only [leechIntegralPairing_add_left, pairing_map,
    show leechIntegralPairing 0 (r.val y) = 0 by simp [leechIntegralPairing, integerDot]]
    using h

/-- Translate the geometrically convenient pairings back to the append contract. -/
theorem extension_of_reverse_pairing {r : LeechIsometryGroup} {n : ℕ}
    (c : CubicRootChain r n)
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0)
    (y : leech) (ho : ∀ i, leechIntegralPairing (c.root i) y = 0)
    (hr : ∀ i, leechIntegralPairing (r.val (c.root i)) y =
      if i.val + 1 = n then 2 else 0) :
    ∀ i, leechIntegralPairing (c.root i) (r.val y) =
      if i.val + 1 = n then -2 else 0 := by
  intro i
  have h := orbit_cross_sum hp (c.root i) y
  rw [ho, hr] at h
  split_ifs at h ⊢ <;> omega

end ChainExtension

namespace CubicRootChain
open ChainExtension
variable {r : LeechIsometryGroup} {n : ℕ}

/-- The first two orbits have exactly the marked D₄ Gram matrix. -/
def initialD4 (c : CubicRootChain r n) (hn : 2 ≤ n) : D4Configuration where
  root := ![c.root (Fin.castLE hn 0), c.root (Fin.castLE hn 1),
    r.val (c.root (Fin.castLE hn 0)), r.val (c.root (Fin.castLE hn 1))]
  gram := by
    intro i j
    have hleft (a b : Fin n) :
        leechIntegralPairing (r.val (c.root a)) (c.root b) =
          leechIntegralPairing (c.root b) (r.val (c.root a)) := leechIntegralPairing_comm _ _
    fin_cases i <;> fin_cases j <;>
      simp [d4Gram, pairing_map, hleft, c.orthogonal, c.mixed, Fin.ext_iff]

/-- Coordinate placement alone supplies the length-two extension. -/
theorem extend_two_of_d4_placement (hplace : D4FramePlacement)
    (c : CubicRootChain r 2)
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) :
    ∃ y : leech, integerDot y.val y.val = 32 ∧
      (∀ i, leechIntegralPairing (c.root i) y = 0) ∧
      ∀ i, leechIntegralPairing (c.root i) (r.val y) =
        if i.val + 1 = 2 then -2 else 0 := by
  obtain ⟨g, hg⟩ := hplace (c.initialD4 le_rfl)
  let y := g.val.symm standardNeighbor
  have hy : g.val y = standardNeighbor := g.val.apply_symm_apply _
  have hpull (i : Fin 4) :
      leechIntegralPairing ((c.initialD4 le_rfl).root i) y =
        if i = 3 then 2 else 0 := by
    rw [← pairing_map g, hg, hy]
    exact standardNeighbor_pairing i
  have ho : ∀ i, leechIntegralPairing (c.root i) y = 0 := by
    intro i
    fin_cases i
    · simpa [initialD4] using hpull 0
    · simpa [initialD4] using hpull 1
  refine ⟨y, ?_, ho, extension_of_reverse_pairing c hp y ho ?_⟩
  · have h := g.prop y y
    rw [hy, standardNeighbor_norm] at h
    exact h.symm
  · intro i
    fin_cases i
    · simpa [initialD4] using hpull 2
    · simpa [initialD4] using hpull 3

/-- The normalized six-vector completion supplies the length-three extension. -/
theorem extend_three_of_coordinate_geometry (hplace : D4FramePlacement)
    (hcomplete : NormalizedThirdOrbitCompletion) (c : CubicRootChain r 3)
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) :
    ∃ y : leech, integerDot y.val y.val = 32 ∧
      (∀ i, leechIntegralPairing (c.root i) y = 0) ∧
      ∀ i, leechIntegralPairing (c.root i) (r.val y) =
        if i.val + 1 = 3 then -2 else 0 := by
  obtain ⟨g, hg⟩ := hplace (c.initialD4 (by decide))
  let v := g.val (c.root 2)
  let w := g.val (r.val (c.root 2))
  have hv : integerDot v.val v.val = 32 := (g.prop _ _).trans (c.root_norm 2)
  have hw : integerDot w.val w.val = 32 :=
    (g.prop _ _).trans ((r.prop _ _).trans (c.root_norm 2))
  have hvp : ∀ i, leechIntegralPairing (standardD4 i) v = if i = 3 then 2 else 0 := by
    intro i
    rw [← hg]
    change leechIntegralPairing (g.val _) (g.val _) = _
    rw [pairing_map]
    fin_cases i <;>
      simp [initialD4, c.orthogonal, leechIntegralPairing_comm _ (c.root 2), c.mixed]
  have hwp : ∀ i, leechIntegralPairing (standardD4 i) w = if i = 1 then -2 else 0 := by
    intro i
    rw [← hg]
    change leechIntegralPairing (g.val _) (g.val _) = _
    rw [pairing_map]
    fin_cases i <;> simp [initialD4, c.mixed, pairing_map, c.orthogonal]
  have hvw : leechIntegralPairing v w = -2 := by
    change leechIntegralPairing (g.val _) (g.val _) = _
    rw [pairing_map, c.mixed]
    simp
  obtain ⟨z, hz, hframe, hvz, hwz⟩ := hcomplete v w hv hw hvp hwp hvw
  let y := g.val.symm z
  have hy : g.val y = z := g.val.apply_symm_apply _
  have hpull (i : Fin 4) :
      leechIntegralPairing ((c.initialD4 (by decide)).root i) y = 0 := by
    rw [← pairing_map g, hg, hy]
    exact hframe i
  have hvy : leechIntegralPairing (c.root 2) y = 0 := by
    rw [← pairing_map g, hy]
    exact hvz
  have hwy : leechIntegralPairing (r.val (c.root 2)) y = 2 := by
    rw [← pairing_map g, hy]
    exact hwz
  have ho : ∀ i, leechIntegralPairing (c.root i) y = 0 := by
    intro i
    fin_cases i
    · simpa [initialD4] using hpull 0
    · simpa [initialD4] using hpull 1
    · exact hvy
  refine ⟨y, ?_, ho, extension_of_reverse_pairing c hp y ho ?_⟩
  · have h := g.prop y y
    rw [hy, hz] at h
    exact h.symm
  · intro i
    fin_cases i
    · simpa [initialD4] using hpull 2
    · simpa [initialD4] using hpull 3
    · exact hwy

end CubicRootChain

/-- Conditional assembly of the exact published chain-extension contract.
The two coordinate geometry statements must still be discharged. -/
theorem cubicChainExtension_of_coordinate_geometry
    (hplace : ChainExtension.D4FramePlacement)
    (hcomplete : ChainExtension.NormalizedThirdOrbitCompletion) : CubicChainExtension := by
  intro r _ hp n hn c
  rcases hn with rfl | rfl
  · exact c.extend_two_of_d4_placement hplace hp
  · exact c.extend_three_of_coordinate_geometry hplace hcomplete hp

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness
