module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.SextetStabilizer.GraphBound.Certificates

/-!
# The full graph-and-sextet stabilizer has order at most 138240

Restriction to the six vertices has image of order at most 720. In its kernel,
small certified adjacency samples bound the successive orbits of vertices 0
and 1 by 64 and 3. Their common stabilizer also fixes 2 and 3 and hence is trivial
by the established four-point base. Orbit–stabilizer gives 192 for the kernel
and 138240 for the full group. This uses no identification with He:2.

Source: ATLAS HeG1-p2058B0; the finite certificates are documented in
`SextetStabilizer/Source/README.md`.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
open Subgroup Held.NormalizerGraph Held.NormalizerGraph.CardBound SextetGraphBound

private theorem orbit_upper_of_mem {G : Type*} [Group G] [Finite G]
    [MulAction G (Fin 2058)] (b : Fin 2058) (s : Finset (Fin 2058))
    (hs : ∀ g : G, g • b ∈ s) :
    Nat.card G ≤ s.card * Nat.card (MulAction.stabilizer G b) := by
  have ho : Nat.card (MulAction.orbit G b) ≤ s.card := by
    have hmem (x : MulAction.orbit G b) : x.val ∈ s := by
      obtain ⟨g, hg⟩ := x.property
      rw [← hg]
      exact hs g
    have he := Nat.card_le_card_of_injective
      (fun x : MulAction.orbit G b => (⟨x.val, hmem x⟩ : ↥s))
      (fun x y h => Subtype.ext (congrArg (fun z : ↥s => z.val) h))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using he
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G b)
  rw [Nat.card_prod] at he
  rw [← he]
  exact Nat.mul_le_mul_right _ ho

private abbrev S0 := ↥sextetRestriction.ker
private abbrev S1 := ↥(MulAction.stabilizer S0 (0 : Fin 2058))
private abbrev S2 := ↥(MulAction.stabilizer S1 (1 : Fin 2058))

private theorem fixes_base (g : S0) : ∀ b ∈ sextetBase, g.val.val b = b := by
  intro b hb
  exact fixes_sextet g b ((mem_sextetBase b).mp hb)

private theorem terminal_eq_one (g : S2) : g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hgraph : g.val.val.val.val ∈ preservingGroup := g.val.val.val.property.1
  have h0 : g.val.val.val.val 0 = 0 := g.val.property
  have h1 : g.val.val.val.val 1 = 1 := g.property
  have h2 := two_fixed _ hgraph (fixes_base g.val.val) h0 h1
  have h3 := three_fixed _ hgraph (fixes_base g.val.val) h0 h1
  apply four_fixed_eq_one _ hgraph
  intro z hz
  have he : z.val = 0 ∨ z.val = 1 ∨ z.val = 2 ∨ z.val = 3 := by omega
  rcases he with he | he | he | he
  · simpa only [show z = 0 from Fin.ext he] using h0
  · simpa only [show z = 1 from Fin.ext he] using h1
  · simpa only [show z = 2 from Fin.ext he] using h2
  · simpa only [show z = 3 from Fin.ext he] using h3

public theorem card_sextetRestriction_ker_le : Nat.card sextetRestriction.ker ≤ 192 := by
  have h2 : Nat.card S2 = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨1, terminal_eq_one⟩
  have h1 : Nat.card S1 ≤ candidates1.card * Nat.card S2 := by
    apply orbit_upper_of_mem (1 : Fin 2058) candidates1
    intro g
    exact one_image_mem g.val.val.val g.val.val.property.1 (fixes_base g.val) g.property
  have h0 : Nat.card S0 ≤ candidates0.card * Nat.card S1 := by
    apply orbit_upper_of_mem (0 : Fin 2058) candidates0
    intro g
    exact zero_image_mem g.val.val g.val.property.1 (fixes_base g)
  rw [candidates1_card, h2, mul_one] at h1
  rw [candidates0_card] at h0
  change Nat.card S0 ≤ 192
  omega

public theorem card_graphSextetGroup_le : Nat.card graphSextetGroup ≤ 138240 := by
  have hr : Nat.card sextetRestriction.range ≤ 720 := by
    calc
      _ ≤ Nat.card (Equiv.Perm ↥sextet) :=
        Nat.card_le_card_of_injective (fun g : sextetRestriction.range => g.val) Subtype.val_injective
      _ = 720 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]
        decide +kernel
  have he := sextetRestriction.ker.card_mul_index
  rw [index_ker] at he
  rw [← he]
  exact (Nat.mul_le_mul card_sextetRestriction_ker_le hr).trans (by decide)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
