module

public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Comparing normalized residuals before and after a prime-group quotient

A normalizing two-group supplement does not change the embedded two-residual,
so adjoining it reflects both containment and strict containment. A prime-group
kernel normalizing the subgroups likewise reflects strict containment and
normalization of prime-perfect images. These facts retain the original maps.

The application in Chapter12/Section09/NaturalSource/Components/Overgroups
constructs the strict Sylow-overgroup chain in the source point-component
quotient, rather than inferring that chain from abstract model isomorphisms.
Source: Aschbacher--Smith, 12.9.3, printed pp.858--859.
-/

public section
open Subgroup
namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- Adjoining the same normalizing two-group reflects containment of two-perfect subgroups. -/
theorem sup_le_sup_iff_of_twoPerfect (A B T : Subgroup G)
    (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B) (hT : IsPGroup 2 T)
    (hTA : T ≤ normalizer (A : Set G)) (hTB : T ≤ normalizer (B : Set G)) :
    A ⊔ T ≤ B ⊔ T ↔ A ≤ B := by
  constructor
  · intro h
    have hm := embedded_pResidual_mono 2 h
    rwa [embedded_pResidual_join_pGroup A T hA hT hTA,
      embedded_pResidual_join_pGroup B T hB hT hTB] at hm
  · exact fun h => sup_le_sup_right h T

/-- Adjoining the same normalizing two-group preserves and reflects strict containment. -/
theorem sup_lt_sup_iff_of_twoPerfect (A B T : Subgroup G)
    (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B) (hT : IsPGroup 2 T)
    (hTA : T ≤ normalizer (A : Set G)) (hTB : T ≤ normalizer (B : Set G)) :
    A ⊔ T < B ⊔ T ↔ A < B := by
  simp only [lt_iff_le_not_ge,
    sup_le_sup_iff_of_twoPerfect A B T hA hB hT hTA hTB,
    sup_le_sup_iff_of_twoPerfect B A T hB hA hT hTB hTA]

/-- A prime-group kernel normalizing both prime-perfect subgroups preserves strict containment. -/
theorem map_lt_map_iff_of_pPerfect {p : ℕ} (f : G →* Q) (A B : Subgroup G)
    (hA : IsPPerfect p A) (hB : IsPPerfect p B) (hk : IsPGroup p f.ker)
    (hkA : f.ker ≤ normalizer (A : Set G))
    (hkB : f.ker ≤ normalizer (B : Set G)) :
    A.map f < B.map f ↔ A < B := by
  have hab : A.map f ≤ B.map f ↔ A ≤ B :=
    ⟨isPPerfect_le_of_map_le_of_kernel_normalizes f A B hA hk hkB, map_mono⟩
  have hba : B.map f ≤ A.map f ↔ B ≤ A :=
    ⟨isPPerfect_le_of_map_le_of_kernel_normalizes f B A hB hk hkA, map_mono⟩
  simp only [lt_iff_le_not_ge, hab, hba]

/-- Normalization of the literal image reflects normalization upstairs when the kernel normalizes the prime-perfect subgroup. -/
theorem map_le_normalizer_map_iff_of_pPerfect {p : ℕ} (f : G →* Q) (A B : Subgroup G)
    (hA : IsPPerfect p A) (hk : IsPGroup p f.ker)
    (hkA : f.ker ≤ normalizer (A : Set G)) :
    B.map f ≤ normalizer (A.map f : Set Q) ↔ B ≤ normalizer (A : Set G) := by
  rw [map_le_iff_le_comap,comap_normalizer_map_of_pPerfect f A hA hk hkA]
end Subgroup

