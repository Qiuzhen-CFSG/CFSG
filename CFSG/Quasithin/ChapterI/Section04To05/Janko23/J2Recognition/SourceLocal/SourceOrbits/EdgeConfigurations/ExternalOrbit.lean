module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.Basic

/-!
# Completing the external common-neighbor orbit from local incidence

Transitivity of F ⊔ X on the outer set and uniqueness of the common neighbor
in each X-orbit imply transitivity of F itself on the outer common neighbors.
The intrinsic F-stabilizer is the actual intersection F ∩ Fᵍ; when that
intersection is D₁₀, orbit-stabilizer gives six vertices.

These implications connect the two independent remaining calculations in
Aschbacher, *Sporadic Groups* (1994), 47.6(2),(5), p.264. They do not assume
triangle transitivity and do not construct the outstanding double cosets
or the local incidence premise.
-/

@[expose] public section

open Subgroup MulAction
open scoped Pointwise
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G]

/-- Restriction identifies the intrinsic F-stabilizer with the literal
ambient intersection, using the left-conjugation convention. -/
noncomputable def fixerStabilizerEquiv (D : Seed G) (Y : D.Vertex)
    (g : localNormalizer D) :
    stabilizer (fixer D Y) ((g : G) • Y) ≃* intersection D Y g := by
  have hle : intersection D Y g ≤ fixer D Y := inf_le_left
  have he : stabilizer (fixer D Y) ((g : G) • Y) =
      (intersection D Y g).subgroupOf (fixer D Y) := by
    ext f
    change (f : G) • ((g : G) • Y) = (g : G) • Y ↔
      (f : G) ∈ fixer D Y ∧
      (f : G) ∈ (fixer D Y).map (MulAut.conj (g : G)).toMonoidHom
    rw [map_fixer]
    change _ ↔ (f : G) ∈ fixer D Y ∧
      (f : G) • D.base = D.base ∧ (f : G) • ((g : G) • Y) = (g : G) • Y
    have hf : (f : G) • D.base = D.base := f.property.1
    simp only [f.property, hf, true_and]
  exact (MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe hle)

/-- The order-ten intersection gives a genuine F-orbit of length six. -/
theorem fixer_orbit_card_of_dihedral_intersection (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (g : localNormalizer D) (hI : Nonempty (intersection D Y g ≃* DihedralGroup 5)) :
    Nat.card (orbit (fixer D Y) ((g : G) • Y)) = 6 := by
  have h := Nat.card_congr (orbitProdStabilizerEquivGroup (fixer D Y) ((g : G) • Y))
  rw [Nat.card_prod, Nat.card_congr (fixerStabilizerEquiv D Y g).toEquiv,
    Nat.card_congr hI.some.toEquiv, DihedralGroup.nat_card,
    Nat.card_congr hF.some.toEquiv, nat_card_alternatingGroup] at h
  norm_num at h
  rw [Nat.card_coe_set_eq]
  omega

/-- Local uniqueness removes the X-component of a transporter. The result is
an actual pointwise fixer element, hence also a setwise edge transporter. -/
theorem outer_common_transitive (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (htrans : ∀ U ∈ outerSet D Y, ∀ V ∈ outerSet D Y,
      ∃ g : actor D Y, (g : G) • U = V)
    (hunique : ∀ U ∈ outerSet D Y,
      ∃! W : D.Vertex, W ∈ orbit D.X U ∧ D.graph.Adj Y W)
    (U V : D.Vertex) (hU : U ∈ outerSet D Y) (hV : V ∈ outerSet D Y)
    (hUY : D.graph.Adj Y U) (hVY : D.graph.Adj Y V) :
    ∃ f : fixer D Y, (f : G) • U = V := by
  obtain ⟨g, hg⟩ := htrans U hU V hV
  have hFN : fixer D Y ≤ normalizer (D.X : Set G) :=
    (fixer_le_localCentralizer D Y hF).trans (centralizer_le_normalizer _)
  have hmem := g.property
  change (g : G) ∈ ((fixer D Y ⊔ D.X : Subgroup G) : Set G) at hmem
  rw [coe_mul_of_left_le_normalizer_right _ _ hFN] at hmem
  obtain ⟨f, hf, x, hx, hfx⟩ := hmem
  change f * x = (g : G) at hfx
  have hfxU : f • (x • U) = V := by rwa [← mul_smul, hfx]
  have hy : f⁻¹ • Y = Y := (fixer D Y).inv_mem hf |>.2
  have hxy : D.graph.Adj Y (x • U) := by
    have h := D.preserves f⁻¹ hVY
    rwa [hy, ← hfxU, inv_smul_smul] at h
  have he : x • U = U := (hunique U hU).unique
    ⟨⟨⟨x, hx⟩, rfl⟩, hxy⟩ ⟨mem_orbit_self U, hUY⟩
  exact ⟨⟨f, hf⟩, by rwa [he] at hfxU⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
