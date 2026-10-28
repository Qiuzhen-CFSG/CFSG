module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.FiberGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Incidences

/-!
# Assembly of the seven-normalizer coset counts

For `A = C_G(S)`, `a = |A|` and `H = N_G(A)`, the elementary argument
gives `|H| = 6a`, a base fiber of size a, and `d = 3`. The geometry and
incidence proofs supply the external subgroup counts. Converting their
literal element counts into right-coset counts gives `b₂ = 12a`,
`b₃ = 4a`, `b₆ = a`, and `b₁ ≥ 4a`.

The final theorem constructs the geometry and discharges all four incidence
premises from the supplied `BenderSevenStructure`. Its structure witness
remains explicit for the source-theorem assembly. The final contradiction
of (4.3) belongs to `SevenCountReduction`.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- The genuine incidence equations give the requested literal coset
counts. The geometry and the four incidence equations are intermediate
premises, not assumptions of the source theorem. -/
public theorem bender_seven_counts_of_incidences
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    (S : Subgroup G) (hSN : S ≤ normalizer (h.sylow : Set G)) (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S) (geometry : BenderSevenGeometry S)
    (hsix : Nat.card (BenderInvolutionsInFibers
      (normalizer (centralizer (S : Set G) : Set G)) 6) =
        6 * Nat.card (centralizer (S : Set G)))
    (htwo : Nat.card (BenderInvolutionsInFibers
      (normalizer (centralizer (S : Set G) : Set G)) 2) +
        Nat.card (BenderInvolutionsInFibers
          (normalizer (centralizer (S : Set G) : Set G)) 6) =
        30 * Nat.card (centralizer (S : Set G)))
    (hthree : Nat.card (BenderInvolutionsInFibers
      (normalizer (centralizer (S : Set G) : Set G)) 3) +
        Nat.card (BenderInvolutionsInFibers
          (normalizer (centralizer (S : Set G) : Set G)) 6) =
        6 * d * Nat.card (centralizer (S : Set G)))
    (hcentral : Nat.card (BenderCentralizedSingletons
      (normalizer (centralizer (S : Set G) : Set G))) =
        2 * (d - 1) * Nat.card (centralizer (S : Set G))) :
    BenderSevenCountData S := by
  have hd := structureData.d_eq_three localData hS hSN
  rw [hd] at hthree hcentral
  rw [bender_involutionsInFibers_card] at hsix
  rw [bender_involutionsInFibers_card, bender_involutionsInFibers_card] at htwo hthree
  let H := normalizer (centralizer (S : Set G) : Set G)
  let a := Nat.card (centralizer (S : Set G))
  have hb6 : benderCosetCount H 6 = a := by dsimp [H, a]; omega
  have hb2 : benderCosetCount H 2 = 12 * a := by dsimp [H, a]; omega
  have hb3 : benderCosetCount H 3 = 4 * a := by dsimp [H, a]; omega
  have hb1 : 4 * a ≤ benderCosetCount H 1 := by
    obtain ⟨m, hm⟩ := bender_single_cosets H
    have hc : Nat.card (BenderCentralizedSingletons H) = 4 * a := hcentral
    omega
  exact {
    normalizer_card := structureData.normalizer_card localData hS
    base_fiber := structureData.base_fiber localData hS
    fiber_sizes := geometry.fiber_sizes
    single_lower := hb1
    double_cosets := hb2
    triple_cosets := hb3
    sextuple_cosets := hb6 }

/-- The supplied local structure proves all the literal coset counts in
`N_G(C_G(S))` used in the contrary case of Bender (4.3). -/
public theorem bender_seven_counts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    (S : Subgroup G) (hSN : S ≤ normalizer (h.sylow : Set G)) (hS : Nat.card S = 7)
    (heven : Even (Nat.card (normalizer (S : Set G))))
    (hcontrary : centralizer (S : Set G) ≠ S)
    (structureData : BenderSevenStructure h S) : BenderSevenCountData S := by
  have geometry := h.bender_seven_geometry localData S hS structureData
  obtain ⟨hsix, htwo, hthree, hcentral⟩ :=
    h.bender_seven_incidences localData S hSN hS heven hcontrary structureData geometry
  exact h.bender_seven_counts_of_incidences localData S hSN hS structureData geometry
    hsix htwo hthree hcentral

end CFSG.Quasithin.Janko1CentralizerData
