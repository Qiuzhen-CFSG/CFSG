module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.SourceContext

/-!
# Geometric contracts for the neighboring closures in MS93 (1.7)

These are explicit intermediate obligations, not source hypotheses. Every
subgroup is a literal conjugate of the seed, its local normal closure, its
pairing kernel, or the fixed space of an actual local two-core. The two
pencils record the local spanning and intersection calculations used on
pp.847--848. In particular neither record assumes centralizer propagation,
a cyclic pairing quotient, or the final elementwise commutator identity.

`FixedGeometry.of_fixed` and `DualGeometry.of_dual` construct these records
from `SourceData`, the permitted `LocalFacts`, and the respective branch
hypotheses. In the second case the source's natural quotient and the
independently constructed contragredient coordinates are available inputs.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
open Subgroup
universe u
variable {M : Type u} [Group M]

/-- Conjugation here is the actual ambient inner automorphism. -/
def conjugate (g : M) (A : Subgroup M) : Subgroup M :=
  A.map (MulAut.conj g).toMonoidHom

/-- The ambient version of the intrinsic left radical, with its carrier retained. -/
def pairingKernel (X W : Subgroup M) : Subgroup M :=
  generated X ⊓ centralizer (W : Set M)

/-- The two other seed lines in the neighboring natural two-space, together
with the one-dimensional seed and its local value spaces. -/
structure FixedPencil (e : Extension (M := M)) (i : Bool) (Z W X : Subgroup M)
    [Z.Normal] : Prop where
  seed_bound : ⁅X, W⁆ ≤ localFixed e Z i
  local_bound : ⁅localGenerated (localParabolic e (!i)) X, W⁆ ≤ localFixed e Z (!i)
  local_proper : ¬ Z ≤ localFixed e Z (!i)
  seed_fixed : localFixed e Z i ≤ centralizer (localResidual (localParabolic e i) : Set M)
  seed_card : Nat.card (localFixed e Z i) ≤ 2
  seed_generator : ∃ x : X,
    X ≤ zpowers (x : M) ⊔ fixedPreimage (component e.projection e.flag) X Z
  neighbors : ∃ a b : M, a ∈ localParabolic e (!i) ∧ b ∈ localParabolic e (!i) ∧
    localGenerated (localParabolic e (!i)) X ≤
      (X ⊔ conjugate a X) ⊔
        (fixedPreimage (component e.projection e.flag) X Z ⊓
          localGenerated (localParabolic e (!i)) X) ∧
    localGenerated (localParabolic e (!i)) X ≤
      (X ⊔ conjugate b X) ⊔
        (fixedPreimage (component e.projection e.flag) X Z ⊓
          localGenerated (localParabolic e (!i)) X) ∧
    conjugate a (localFixed e Z i) ⊓ conjugate b (localFixed e Z i) = ⊥
  residual_generation : component e.projection e.flag ≤
    normalClosure (localResidual (localParabolic e i) : Set M)

/-- In the dual case neighboring planes cover the global quotient, and
opposite local value lines have trivial intersection. -/
structure DualPencil (e : Extension (M := M)) (i : Bool) (Z W X : Subgroup M) : Prop where
  seed_bound : ⁅X, W⁆ ≤ localFixed e Z i
  star_cover : generated X ≤
    (⨆ p : localParabolic e i,
      conjugate (p : M) (localGenerated (localParabolic e (!i)) X)) ⊔ pairingKernel X W
  star_neighbors : ∀ p : localParabolic e i, ∃ r s : localParabolic e (!i),
    conjugate (p : M) (localGenerated (localParabolic e (!i)) X) ≤
      (X ⊔ conjugate ((p : M) * (r : M)) X) ⊔ pairingKernel X W ∧
    conjugate (p : M) (localGenerated (localParabolic e (!i)) X) ≤
      (X ⊔ conjugate ((p : M) * (s : M)) X) ⊔ pairingKernel X W ∧
    conjugate ((p : M) * (r : M)) (localFixed e Z i) ⊓
      conjugate ((p : M) * (s : M)) (localFixed e Z i) ≤
        conjugate (p : M) (localFixed e Z (!i)) ∧
    conjugate (p : M) (localFixed e Z (!i)) ≤ localFixed e Z i
  opposite_cover : ∃ a b : M,
    conjugate a X ≤ localGenerated (localParabolic e (!i)) X ∧
    conjugate b X ≤ localGenerated (localParabolic e (!i)) X ∧
    generated X ≤
      (localGenerated (localParabolic e (!i)) X ⊔
        conjugate a (localGenerated (localParabolic e (!i)) X)) ⊔ pairingKernel X W ∧
    generated X ≤
      (localGenerated (localParabolic e (!i)) X ⊔
        conjugate b (localGenerated (localParabolic e (!i)) X)) ⊔ pairingKernel X W ∧
    conjugate a (localFixed e Z (!i)) ⊓ conjugate b (localFixed e Z (!i)) = ⊥
  core_fixed : ⁅localGenerated (localParabolic e (!i)) X,
    localCore (localParabolic e (!i))⁆ ≤ centralizer (W : Set M)
  residual_generation : localResidual (localParabolic e i) ≤
    localGenerated (localParabolic e i) (localCore (localParabolic e (!i)))
  local_irreducible : ∀ D : Subgroup M, D ≤ localFixed e Z i →
    localResidual (localParabolic e i) ≤ normalizer (D : Set M) →
    D = ⊥ ∨ D = localFixed e Z i

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
