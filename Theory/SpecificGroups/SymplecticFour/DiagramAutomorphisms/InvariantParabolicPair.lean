module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantLocalPair
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel.Parabolics

/-!
# A common Sylow normalizing the two actual symplectic parabolics

A diagram-preserving automorphism fixing the standard unipotent group fixes
both determinant kernels, hence their full parabolic normalizers. Extending
the standard unipotent subgroup to an ambient Sylow gives simultaneous
normalization of the two parabolics under the original embedding.

Source: Aschbacher--Smith B.6.9, printed p.116: the rank-two alternative
requires nontrivial diagram action in a minimal parabolic.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Fixing the Sylow and the diagram fixes both full flag parabolics. -/
theorem parabolic_pair_map_of_unipotent_map {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (ha : PreservesDiagram a)
    (hU : unipotent.map a.toMonoidHom = unipotent) :
    pointParabolic.map a.toMonoidHom = pointParabolic ∧
      planeParabolic.map a.toMonoidHom = planeParabolic := by
  obtain ⟨hp, hl⟩ := local_pair_map_of_unipotent_map hF hn a ha hU
  constructor
  · rw [← pointLocal_normalizer hF hn, map_equiv_normalizer_eq, hp]
  · rw [← planeLocal_normalizer hF hn, map_equiv_normalizer_eq, hl]

variable {G : Type*} [Group G]

/-- A single ambient Sylow extends the standard model Sylow and normalizes
both embedded parabolics in every normal diagram-preserving extension. -/
theorem exists_sylow_normalizing_parabolic_pair {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction N e g)) :
    ∃ S : Sylow 2 G,
      (S : Subgroup G).comap (N.subtype.comp e.toMonoidHom) = unipotent ∧
      (S : Subgroup G) ≤ normalizer
        (pointParabolic.map (N.subtype.comp e.toMonoidHom) : Set G) ∧
      (S : Subgroup G) ≤ normalizer
        (planeParabolic.map (N.subtype.comp e.toMonoidHom) : Set G) := by
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
    exact lift_normalizes pointParabolic g
      (parabolic_pair_map_of_unipotent_map hF hn _ (hdiagram g) (ha g hg)).1
  · intro g hg
    exact lift_normalizes planeParabolic g
      (parabolic_pair_map_of_unipotent_map hF hn _ (hdiagram g) (ha g hg)).2

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
