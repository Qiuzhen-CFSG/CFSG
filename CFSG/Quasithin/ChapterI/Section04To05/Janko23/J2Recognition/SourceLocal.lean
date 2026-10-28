module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Frame
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Suborbits
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleBase

/-!
# Conditional assembly of the source J₂ local geometry

The local group is the literal C_G(B) of an `EdgeFrame`. From the source
suborbits we prove neighbor transitivity and global generation. The
proper-overgroup calculation in N_G(X), together with an element of K
inverting X, proves vertex generation. Maximality of N_K(X) and an actual
edge reversal prove local generation. Thus none of the three generation
identities is a field of the conditional input.

The final theorem assembles containment of triangles in translates of the
local graph from two orbits of the **setwise** edge stabilizer. The two
vertices completing a triangle inside the generated A₄ are individually
fixed by the pointwise edge fixer; they must not be collapsed to one orbit
of that smaller group. Both source triangle types are retained.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5–47.6 and 47.10,
pp.263–264, 266–267. These are conditional assembly theorems. The source
prime-local calculations, four suborbits, construction of the frame with
K ≃ A₅, normalizer overlaps, and the two triangle orbits still need their
producers. No unconditional `LocalData` is asserted from `Seed` here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem vertex_generation (F : EdgeFrame D)
    (hovergroups : ∀ U : Subgroup G, edgeFixer G D.base F.y ≤ U →
      U ≤ normalizer (D.X : Set G) → U ≠ normalizer (D.X : Set G) →
      U ≤ centralizer (D.X : Set G))
    (hinverts : ¬ F.K ⊓ normalizer (D.X : Set G) ≤ centralizer (D.X : Set G)) :
    edgeFixer G D.base F.y ⊔ (F.K ⊓ normalizer (D.X : Set G)) =
      normalizer (D.X : Set G) := by
  by_contra hn
  apply hinverts
  apply le_sup_right.trans (hovergroups _ le_sup_left _ hn)
  apply sup_le _ inf_le_right
  change MulAction.stabilizer G D.base ⊓ MulAction.stabilizer G F.y ≤ _
  rw [D.stabilizer_eq_normalizer D.base]
  exact inf_le_left

private theorem local_generation (F : EdgeFrame D)
    (hmax : F.K ⊓ normalizer (D.X : Set G) ⋖ F.K)
    (hswap : ∃ t : F.K, (t : G) • D.base = F.y ∧ (t : G) • F.y = D.base) :
    (F.K ⊓ edgeStabilizer G D.base F.y) ⊔
      (F.K ⊓ normalizer (D.X : Set G)) = F.K := by
  rcases hmax.eq_or_eq le_sup_right (sup_le inf_le_left inf_le_left) with he | he
  · obtain ⟨t, htx, hty⟩ := hswap
    have ht : (t : G) ∈ F.K ⊓ edgeStabilizer G D.base F.y :=
      ⟨t.property, Or.inr ⟨htx, hty⟩⟩
    have htm : (t : G) ∈ normalizer (D.X : Set G) :=
      (he ▸ (show F.K ⊓ edgeStabilizer G D.base F.y ≤
        (F.K ⊓ edgeStabilizer G D.base F.y) ⊔
        (F.K ⊓ normalizer (D.X : Set G)) from le_sup_left) ht).2
    have htf : (t : G) ∈ MulAction.stabilizer G D.base := by
      rw [D.stabilizer_eq_normalizer]
      exact htm
    exact False.elim (F.adjacent.ne (htf.symm.trans htx))
  · exact he

/-- Assemble all three generation identities from the actual local calculations. -/
def localDataOfCalculations (R : FourSuborbits D) (F : EdgeFrame D)
    (hovergroups : ∀ U : Subgroup G, edgeFixer G D.base F.y ≤ U →
      U ≤ normalizer (D.X : Set G) → U ≠ normalizer (D.X : Set G) →
      U ≤ centralizer (D.X : Set G))
    (hinverts : ¬ F.K ⊓ normalizer (D.X : Set G) ≤ centralizer (D.X : Set G))
    (hmax : F.K ⊓ normalizer (D.X : Set G) ⋖ F.K)
    (hswap : ∃ t : F.K, (t : G) • D.base = F.y ∧ (t : G) • F.y = D.base) :
    LocalData D where
  y := F.y
  adjacent := F.adjacent
  K := F.K
  neighbors := R.neighbors F.y F.adjacent
  local_orbit := hswap.imp fun _ h => h.1
  generate := R.generate_of_moves_to_neighbor F.K F.y F.adjacent
    (hswap.imp fun _ h => h.1)
  vertex_generate := by exact vertex_generation F hovergroups hinverts
  local_generate := by exact local_generation F hmax hswap

variable [IsSimpleGroup G]

/-- Both triangle types are covered by translates of the actual local edge orbit. -/
theorem triangles_of_two_edgeStabilizer_orbits (L : LocalData D) (T₁ T₂ : D.Vertex)
    (h₁ : L.simpleSystem.localEdge L.y T₁ ∧ L.simpleSystem.localEdge T₁ D.base)
    (h₂ : L.simpleSystem.localEdge L.y T₂ ∧ L.simpleSystem.localEdge T₂ D.base)
    (horbits : ∀ V : D.Vertex, D.graph.Adj D.base V → D.graph.Adj L.y V →
      ∃ e : edgeStabilizer G D.base L.y, (e : G) • V = T₁ ∨ (e : G) • V = T₂) :
    L.simpleSystem.TrianglesInLocalOrbits := by
  intro a b c hab hbc hca
  obtain ⟨g, hg⟩ := D.transitive a
  have hax : g⁻¹ • a = D.base := by rw [← hg, inv_smul_smul]
  have hnear := D.preserves g⁻¹ hab
  rw [hax] at hnear
  obtain ⟨k, hk⟩ := L.neighbors _ hnear
  let q : G := g * k
  have hkx : (k : G) • D.base = D.base := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [D.stabilizer_eq_normalizer]
    exact k.property
  have hqa : q • D.base = a := by simp only [q, mul_smul, hkx, hg]
  have hqb : q • L.y = b := by simp only [q, mul_smul, hk, smul_inv_smul]
  have haq : q⁻¹ • a = D.base := by rw [← hqa, inv_smul_smul]
  have hbq : q⁻¹ • b = L.y := by rw [← hqb, inv_smul_smul]
  have hcX := D.preserves q⁻¹ hca.symm
  have hcY := D.preserves q⁻¹ hbc
  rw [haq] at hcX
  rw [hbq] at hcY
  obtain ⟨e, he⟩ := horbits _ hcX hcY
  have hxy : L.simpleSystem.localEdge D.base L.y :=
    ⟨1, Or.inl ⟨one_smul _ _, one_smul _ _⟩⟩
  have hic : (q * (e : G)⁻¹)⁻¹ • c = T₁ ∨
      (q * (e : G)⁻¹)⁻¹ • c = T₂ := by
    simpa only [mul_inv_rev, inv_inv, mul_smul] using he
  refine ⟨q * (e : G)⁻¹, ?_⟩
  rcases e.property with ⟨hex, hey⟩ | ⟨hex, hey⟩
  · have hia : (q * (e : G)⁻¹)⁻¹ • a = D.base := by
      rw [mul_inv_rev, inv_inv, mul_smul, haq, hex]
    have hib : (q * (e : G)⁻¹)⁻¹ • b = L.y := by
      rw [mul_inv_rev, inv_inv, mul_smul, hbq, hey]
    rw [hia, hib]
    rcases hic with hic | hic
    · rw [hic]
      exact ⟨hxy, h₁⟩
    · rw [hic]
      exact ⟨hxy, h₂⟩
  · have hia : (q * (e : G)⁻¹)⁻¹ • a = L.y := by
      rw [mul_inv_rev, inv_inv, mul_smul, haq, hex]
    have hib : (q * (e : G)⁻¹)⁻¹ • b = D.base := by
      rw [mul_inv_rev, inv_inv, mul_smul, hbq, hey]
    rw [hia, hib]
    rcases hic with hic | hic
    · rw [hic]
      exact ⟨L.simpleSystem.localGraph.symm.symm _ _ hxy,
        L.simpleSystem.localGraph.symm.symm _ _ h₁.2, L.simpleSystem.localGraph.symm.symm _ _ h₁.1⟩
    · rw [hic]
      exact ⟨L.simpleSystem.localGraph.symm.symm _ _ hxy,
        L.simpleSystem.localGraph.symm.symm _ _ h₂.2, L.simpleSystem.localGraph.symm.symm _ _ h₂.1⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
