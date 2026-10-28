module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting.Transfer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting.SylowObstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting.AugmentationComparison
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting.Centralizers

/-!
# Splitting the orthogonal cover and extending the marked coordinates

A nonzero central kernel identifies a perfect cover of the six-dimensional
A₈ module with the seven-dimensional augmentation module. Triviality of its
component centralizer extends these
coordinates to S₈. The Sylow fixed-space obstruction then contradicts the
moving line. The resulting injective projection gives natural-module
coordinates; a second centralizer calculation extends them to the full actor.

The conditional assembly lemmas are retained, and `kernel_eq_bot` and
`coordinates` discharge their model-comparison and centralizer premises.
The coordinates agree with the supplied cover projection and respect every
element of the marked S₈. The fixed-vector obstruction works for any Y, so
neither Y ≤ L nor faithfulness of the original representation is needed here.

The relevant earlier source facts are I.1.5 (universal perfect module coverings)
and I.1.6(1) (one-dimensional H¹ for the six-dimensional A₈ natural module).
The four-dimensional PSL₄(2) module of I.1.6(6) is a different module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.32(1),
printed pp.1132–1133, and I.1.5–I.1.6(1), printed p.408 (PDF p.419).
-/

@[expose] public section

open Equiv

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

variable {K V : Type*} [Group K] [Finite K] [AddCommGroup V] [Module (ZMod 2) V]

/-- The augmentation comparison and its rigidity exclude the nonzero-cover branch. -/
theorem kernel_eq_bot_of_comparison (ρ : Representation (ZMod 2) K V)
    (e : K ≃* Perm (Fin 8)) (L : Subgroup K)
    (hL : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (cover : Models.OrthogonalCover ρ L e) (S : Sylow 2 K) {P Y : Subgroup K}
    (line : Models.MovingLine ρ P (S : Subgroup K) Y)
    (rigid : TrivialComponentCentralizer (BinaryPermutation.coreRepresentation (Fin 8)))
    (compare : cover.projection.ker ≠ ⊥ →
      ∃ f : V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 8),
        ∀ (l : L) v, f (ρ l v) =
          BinaryPermutation.coreRepresentation (Fin 8) (e l) (f v)) :
    cover.projection.ker = ⊥ := by
  by_contra hn
  obtain ⟨f, hf⟩ := compare hn
  exact no_movingLine_core_coordinates ρ e S line f
    (extend_marked_equivariance ρ _ e L hL rigid f hf)

/-- Once the two concrete model facts are supplied, the original cover projection
itself gives coordinates equivariant for the entire marked symmetric group. -/
theorem coordinates_of_comparison (ρ : Representation (ZMod 2) K V)
    (e : K ≃* Perm (Fin 8)) (L : Subgroup K)
    (hL : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (cover : Models.OrthogonalCover ρ L e) (S : Sylow 2 K) {P Y : Subgroup K}
    (line : Models.MovingLine ρ P (S : Subgroup K) Y)
    (core_rigid : TrivialComponentCentralizer (BinaryPermutation.coreRepresentation (Fin 8)))
    (natural_rigid : TrivialComponentCentralizer (BinaryPermutation.naturalRepresentation (Fin 8)))
    (compare : cover.projection.ker ≠ ⊥ →
      ∃ f : V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 8),
        ∀ (l : L) v, f (ρ l v) =
          BinaryPermutation.coreRepresentation (Fin 8) (e l) (f v)) :
    ∃ f : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
      (∀ v, f v = cover.projection v) ∧
      ∀ g v, f (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 8) (e g) (f v) := by
  have hk := kernel_eq_bot_of_comparison ρ e L hL cover S line core_rigid compare
  let f := LinearEquiv.ofBijective cover.projection
    ⟨LinearMap.ker_eq_bot.mp hk, cover.onto⟩
  refine ⟨f, fun _ => rfl, ?_⟩
  exact extend_marked_equivariance ρ _ e L hL natural_rigid f cover.equivariant

variable [FiniteDimensional (ZMod 2) V]

/-- A perfect orthogonal cover admitting the Sylow-invariant moving line has
zero kernel. The nonzero-kernel case would be the augmentation module, whose
Sylow-fixed vectors are fixed by the entire actor. -/
theorem kernel_eq_bot (ρ : Representation (ZMod 2) K V)
    (e : K ≃* Perm (Fin 8)) (L : Subgroup K)
    (hL : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (cover : Models.OrthogonalCover ρ L e) (S : Sylow 2 K) {P Y : Subgroup K}
    (line : Models.MovingLine ρ P (S : Subgroup K) Y) :
    cover.projection.ker = ⊥ :=
  kernel_eq_bot_of_comparison ρ e L hL cover S line core_componentCentralizer_trivial
    (augmentation_coordinates_of_nonzero_kernel ρ e L hL cover)

/-- The cover projection gives natural-module coordinates for the entire
marked symmetric group. All covering and extension premises are discharged. -/
theorem coordinates (ρ : Representation (ZMod 2) K V)
    (e : K ≃* Perm (Fin 8)) (L : Subgroup K)
    (hL : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (cover : Models.OrthogonalCover ρ L e) (S : Sylow 2 K) {P Y : Subgroup K}
    (line : Models.MovingLine ρ P (S : Subgroup K) Y) :
    ∃ f : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
      (∀ v, f v = cover.projection v) ∧
      ∀ g v, f (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 8) (e g) (f v) :=
  coordinates_of_comparison ρ e L hL cover S line core_componentCentralizer_trivial
    natural_componentCentralizer_trivial
    (augmentation_coordinates_of_nonzero_kernel ρ e L hL cover)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

end
