module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.SourceTriangles

/-!
# Distance two in the source J₂ graph

Double-count ordered incidences between the 36 neighbors and each of the
135- and 108-point nonedge suborbits. The proved local intersection counts
15 and 12 imply four common neighbors for either nonedge type. Every pair
is therefore joined by a walk of length at most two, without any additional
source or model premise.

Source: Aschbacher, *Sporadic Groups* (1994), 47.7(1–2), pp.264–265.
Connectivity of the common-neighbor graphs and contraction of pentagons
remain separate obligations of the source recognition proof.
-/

public section
open Subgroup MulAction
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

namespace Distances
open scoped BigOperators

private theorem incidence_balance {V : Type*} [Finite V] (A B : Set V)
    (r : V → V → Prop) (m n : ℕ)
    (ha : ∀ a ∈ A, {b | b ∈ B ∧ r a b}.ncard = m)
    (hb : ∀ b ∈ B, {a | a ∈ A ∧ r a b}.ncard = n) :
    A.ncard * m = B.ncard * n := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  let e : (Σ a : A, {b : V // b ∈ B ∧ r a b}) ≃
      (Σ b : B, {a : V // a ∈ A ∧ r a b}) := {
    toFun := fun ⟨a, b⟩ => ⟨⟨b, b.property.1⟩, ⟨a, a.property, b.property.2⟩⟩
    invFun := fun ⟨b, a⟩ => ⟨⟨a, a.property.1⟩, ⟨b, b.property, a.property.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have he := Nat.card_congr e
  rw [Nat.card_sigma, Nat.card_sigma] at he
  have hma (a : A) : Nat.card {b : V // b ∈ B ∧ r a b} = m := by
    exact (Nat.card_coe_set_eq _).trans (ha a a.property)
  have hnb (b : B) : Nat.card {a : V // a ∈ A ∧ r a b} = n := by
    exact (Nat.card_coe_set_eq _).trans (hb b b.property)
  simpa only [hma, hnb, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using he

omit [IsSimpleGroup G] in
private theorem smul_ncard (D : Seed G) (g : G) (P Q : D.Vertex → Prop)
    (h : ∀ U, P U ↔ Q (g • U)) : {U | P U}.ncard = {U | Q U}.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g) h)

omit [IsSimpleGroup G] in
private theorem adj_smul_iff (D : Seed G) (g : G) (U V : D.Vertex) :
    D.graph.Adj (g • U) (g • V) ↔ D.graph.Adj U V := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using D.preserves g⁻¹ h
  · exact D.preserves g

omit [IsSimpleGroup G] in
private theorem mixed_card (D : Seed G) (r : D.Vertex → D.Vertex → Prop)
    (hr : ∀ (g : G) (A B : D.Vertex), r (g • A) (g • B) ↔ r A B) (n : ℕ)
    (hn : ∀ Y, D.graph.Adj D.base Y → {U | D.graph.Adj D.base U ∧ r Y U}.ncard = n)
    {A B : D.Vertex} (hAB : D.graph.Adj A B) :
    {U | D.graph.Adj A U ∧ r B U}.ncard = n := by
  obtain ⟨g, rfl⟩ := D.transitive A
  have hadj : D.graph.Adj D.base (g⁻¹ • B) := by
    simpa only [inv_smul_smul] using D.preserves g⁻¹ hAB
  have hc := smul_ncard D g
    (fun U => D.graph.Adj D.base U ∧ r (g⁻¹ • B) U)
    (fun U => D.graph.Adj (g • D.base) U ∧ r B U) (fun U => by
      rw [← adj_smul_iff D g D.base U, ← hr g (g⁻¹ • B) U, smul_inv_smul])
  exact hc.symm.trans (hn _ hadj)

omit [IsSimpleGroup G] in
private theorem label_two_iff (D : Seed G) (U : D.Vertex) :
    sl2Join D D.base U ↔ orbitLabel D U = 2 := by
  classical
  refine ⟨orbitLabel_of_sl2Join D, ?_⟩
  intro h
  unfold orbitLabel at h
  split_ifs at h <;> simp_all

private theorem label_three_iff (D : Seed G) (U : D.Vertex) :
    a5Join D D.base U ↔ orbitLabel D U = 3 := by
  refine ⟨orbitLabel_of_a5Join D, ?_⟩
  intro h
  rcases (InvolutionGeometry.Applications.fourSuborbits D).joins D.base U with he | ha | hs | hf
  · subst U
    simp at h
  · have := orbitLabel_of_adj D ha
    omega
  · have := orbitLabel_of_sl2Join D hs
    omega
  · exact hf

private theorem nonedge_balance (D : Seed G) (r : D.Vertex → D.Vertex → Prop)
    (hr : ∀ (g : G) (A B : D.Vertex), r (g • A) (g • B) ↔ r A B) (i : Fin 4) (m : ℕ)
    (hi : ∀ U, r D.base U ↔ orbitLabel D U = i)
    (hm : ∀ Y, D.graph.Adj D.base Y → {U | D.graph.Adj D.base U ∧ r Y U}.ncard = m)
    (Y : D.Vertex) (hY : r D.base Y) :
    36 * m = subdegrees i * {U | D.graph.Adj D.base U ∧ D.graph.Adj Y U}.ncard := by
  let A : Set D.Vertex := {U | D.graph.Adj D.base U}
  let B : Set D.Vertex := {U | r D.base U}
  let c := {U | D.graph.Adj D.base U ∧ D.graph.Adj Y U}.ncard
  have hA : A.ncard = 36 := (InvolutionGeometry.Applications.fourSuborbits D).neighbor_card
  have hB : B.ncard = subdegrees i := by
    have he : B = {U | orbitLabel D U = i} := Set.ext hi
    rw [he, ← Nat.card_coe_set_eq]
    exact (InvolutionGeometry.Applications.fourSuborbits D).card i
  have hc (V : D.Vertex) (hV : V ∈ B) :
      {U | U ∈ A ∧ D.graph.Adj U V}.ncard = c := by
    obtain ⟨g, hg⟩ := (InvolutionGeometry.Applications.fourSuborbits D).transitive V Y
      ((hi V).mp hV |>.trans ((hi Y).mp hY).symm)
    apply smul_ncard D (g : G)
    intro U
    change (D.graph.Adj D.base U ∧ D.graph.Adj U V) ↔
      (D.graph.Adj D.base ((g : G) • U) ∧ D.graph.Adj Y ((g : G) • U))
    have hbase : D.graph.Adj D.base ((g : G) • U) ↔ D.graph.Adj D.base U := by
      simpa only [normalizer_fixes_base D g] using adj_smul_iff D (g : G) D.base U
    rw [hbase, ← hg, adj_smul_iff]
    exact and_congr_right fun _ => D.graph.adj_comm _ _
  have hd := incidence_balance A B D.graph.Adj m c (fun U hU => by
    have he : {V | V ∈ B ∧ D.graph.Adj U V} =
        {V | D.graph.Adj U V ∧ r D.base V} := by ext V; exact and_comm
    rw [he]
    exact mixed_card D r hr m hm hU.symm) hc
  rwa [hA, hB] at hd

/-- Both source nonedge types have exactly four common neighbors (47.7(2)). -/
theorem common_neighbors_card (D : Seed G) (Y : D.Vertex)
    (hY : Y ≠ D.base) (hn : ¬ D.graph.Adj D.base Y) :
    {U | D.graph.Adj D.base U ∧ D.graph.Adj Y U}.ncard = 4 := by
  rcases (InvolutionGeometry.Applications.fourSuborbits D).joins D.base Y with he | ha | hs | hf
  · exact (hY he.symm).elim
  · exact (hn ha).elim
  · have h := nonedge_balance D (sl2Join D) (sl2Join_smul_iff D) 2 15
      (label_two_iff D) (source_sl2_neighbors_card D) Y hs
    change 36 * 15 = 135 * _ at h
    omega
  · have h := nonedge_balance D (a5Join D) (a5Join_smul_iff D) 3 12
      (label_three_iff D) (source_a5_neighbors_card D) Y hf
    change 36 * 12 = 108 * _ at h
    omega

/-- The actual source graph has diameter at most two (47.7(1)). -/
theorem short (D : Seed G) (A B : D.Vertex) :
    A = B ∨ D.graph.Adj A B ∨ ∃ U, D.graph.Adj A U ∧ D.graph.Adj U B := by
  classical
  obtain ⟨g, rfl⟩ := D.transitive A
  by_cases he : g⁻¹ • B = D.base
  · left
    rw [← he, smul_inv_smul]
  by_cases ha : D.graph.Adj D.base (g⁻¹ • B)
  · right; left
    simpa only [smul_inv_smul] using D.preserves g ha
  have hc := common_neighbors_card D (g⁻¹ • B) he ha
  obtain ⟨U, hUX, hUB⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hc]; decide)
  refine Or.inr (Or.inr ⟨g • U, D.preserves g hUX, ?_⟩)
  simpa only [smul_inv_smul] using D.preserves g hUB.symm

/-- The bounded walks used by the source square-and-pentagon contraction. -/
theorem short_walk (D : Seed G) (A B : D.Vertex) :
    ∃ p : D.graph.Walk A B, p.length ≤ 2 := by
  rcases short D A B with he | ha | ⟨U, hAU, hUB⟩
  · subst B
    exact ⟨.nil, by simp⟩
  · exact ⟨ha.toWalk, by simp⟩
  · exact ⟨.cons hAU hUB.toWalk, by simp⟩

end Distances

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
