module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.LocalActions
public import Theory.SpecificGroups.SymplecticFour.Sylow

/-!
# A common Sylow subgroup normalizing both symplectic local factors

A diagram-preserving automorphism fixing the standard unipotent subgroup
has an inner-field decomposition whose inner part lies in its Borel
normalizer. Both parts therefore preserve both determinant kernels.

For a normal embedded Sp₄, extend its standard Sylow subgroup to an ambient
Sylow. The inverse image of the ambient Sylow is precisely the standard
unipotent subgroup. Conjugation by that ambient Sylow fixes this inverse
image, so it normalizes both embedded local factors. All maps use the same
given embedding; no separate conjugators for the two parabolic types occur.

Source: the diagram-preserving parabolic setup for Aschbacher--Smith
E.1.14(1), printed p.214, and F.1.12, printed pp.263--264.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Stabilizing the unipotent subgroup and preserving the diagram forces
simultaneous preservation of the two actual local factors. -/
theorem local_pair_map_of_unipotent_map {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (ha : PreservesDiagram a)
    (hU : unipotent.map a.toMonoidHom = unipotent) :
    pointLocal.map a.toMonoidHom = pointLocal ∧
      planeLocal.map a.toMonoidHom = planeLocal := by
  obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
  have hp := pointLocal_map hF hn (fieldAutomorphism σ) (field_map_pointParabolic σ)
  have hl := planeLocal_map hF hn (fieldAutomorphism σ) (field_map_planeParabolic σ)
  have hu : unipotent.map (fieldAutomorphism σ).toMonoidHom = unipotent := by
    rw [unipotent, map_inf _ _ _ (fieldAutomorphism σ).injective, hp, hl]
  have hg : g ∈ borel (F := F) := by
    rw [borel_eq_normalizer_unipotent, mem_normalizer_iff_map_conj_eq]
    calc
      unipotent.map (MulAut.conj g).toMonoidHom =
          (unipotent.map (fieldAutomorphism σ).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by rw [hu]
      _ = unipotent := by rw [Subgroup.map_map]; exact hU
  have hpN : g ∈ normalizer (pointLocal (F := F) : Set (Sp F)) :=
    le_normalizer_of_normal_subgroupOf pointLocal_le hg.1
  have hlN : g ∈ normalizer (planeLocal (F := F) : Set (Sp F)) :=
    le_normalizer_of_normal_subgroupOf planeLocal_le hg.2
  constructor
  · calc
      _ = (pointLocal.map (fieldAutomorphism σ).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ = pointLocal := by rw [hp]; exact mem_normalizer_iff_map_conj_eq.mp hpN
  · calc
      _ = (planeLocal.map (fieldAutomorphism σ).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ = planeLocal := by rw [hl]; exact mem_normalizer_iff_map_conj_eq.mp hlN

variable {G : Type*} [Group G]

/-- A single ambient Sylow extends the standard model Sylow and normalizes
both embedded locals in every normal diagram-preserving extension. -/
theorem exists_sylow_normalizing_local_pair {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction N e g)) :
    ∃ S : Sylow 2 G,
      (S : Subgroup G).comap (N.subtype.comp e.toMonoidHom) = unipotent ∧
      (S : Subgroup G) ≤ normalizer
        (pointLocal.map (N.subtype.comp e.toMonoidHom) : Set G) ∧
      (S : Subgroup G) ≤ normalizer
        (planeLocal.map (N.subtype.comp e.toMonoidHom) : Set G) := by
  let f := N.subtype.comp e.toMonoidHom
  obtain ⟨S, hS⟩ := (unipotentSylow hF (by omega : 1 ≤ n)).exists_comap_eq_of_injective
    (f := f) (N.subtype_injective.comp e.injective)
  change (S : Subgroup G).comap f = unipotent at hS
  have ha (g : G) (hg : g ∈ S) :
      unipotent.map (extensionAction N e g).toMonoidHom = unipotent := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hS] at hx ⊢
      change f (extensionAction N e g x) ∈ S
      rw [show f (extensionAction N e g x) = g * f x * g⁻¹ from
        extensionAction_apply N e g x]
      exact S.mul_mem (S.mul_mem hg hx) (S.inv_mem hg)
    · rw [card_map_of_injective (extensionAction N e g).injective]
  have lift_normalizes (D : Subgroup (Sp F)) (g : G)
      (hD : D.map (extensionAction N e g).toMonoidHom = D) :
      g ∈ normalizer (D.map f : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      (D.map f).map (MulAut.conj g).toMonoidHom =
          (D.map (extensionAction N e g).toMonoidHom).map f := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        exact (extensionAction_apply N e g x).symm
      _ = D.map f := by rw [hD]
  refine ⟨S, hS, ?_, ?_⟩
  · intro g hg
    exact lift_normalizes pointLocal g
      (local_pair_map_of_unipotent_map hF hn _ (hdiagram g) (ha g hg)).1
  · intro g hg
    exact lift_normalizes planeLocal g
      (local_pair_map_of_unipotent_map hF hn _ (hdiagram g) (ha g hg)).2

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
