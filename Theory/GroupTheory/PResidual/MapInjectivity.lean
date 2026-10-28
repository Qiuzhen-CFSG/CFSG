module

public import Theory.GroupTheory.PResidual.NormalizerImage

/-!
# Detecting p-perfect subgroups through a p-group kernel

If the kernel of a homomorphism is a p-group and normalizes two p-perfect
subgroups, equality of their images implies equality of the subgroups.
Indeed, the preimage of either image is the subgroup joined with the kernel;
its p-residual recovers the original subgroup. In particular a central
p-group quotient loses no information about p-perfect subgroups.

This is the subgroup transport needed for central covers in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 16.1.2 and
Notation 16.5.5, printed pp.1170 and 1197.
-/

public section

namespace Subgroup

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

/-- Equality of images detects p-perfect subgroups when the p-group kernel
normalizes both. Surjectivity and ambient normality of the subgroups are
not required. -/
theorem eq_of_map_eq_map_of_isPPerfect (f : G →* H) {A B : Subgroup G}
    (hA : IsPPerfect p A) (hB : IsPPerfect p B)
    (hk : IsPGroup p f.ker)
    (hnA : f.ker ≤ normalizer (A : Set G))
    (hnB : f.ker ≤ normalizer (B : Set G))
    (he : A.map f = B.map f) : A = B := by
  have hs : A ⊔ f.ker = B ⊔ f.ker := by
    simpa only [comap_map_eq] using congrArg (fun U : Subgroup H => U.comap f) he
  calc
    A = (pResidual p (A ⊔ f.ker : Subgroup G)).map (A ⊔ f.ker).subtype :=
      (embedded_pResidual_sup_kernel f A hA hk hnA).symm
    _ = (pResidual p (B ⊔ f.ker : Subgroup G)).map (B ⊔ f.ker).subtype := by rw [hs]
    _ = B := embedded_pResidual_sup_kernel f B hB hk hnB

/-- A central p-group kernel detects equality of all p-perfect subgroups. -/
theorem map_eq_map_iff_of_isPPerfect_of_central_kernel (f : G →* H)
    {A B : Subgroup G} (hA : IsPPerfect p A) (hB : IsPPerfect p B)
    (hk : IsPGroup p f.ker) (hc : f.ker ≤ center G) :
    A.map f = B.map f ↔ A = B := by
  constructor
  · apply eq_of_map_eq_map_of_isPPerfect f hA hB hk
    · exact hc.trans ((center_le_centralizer (A : Set G)).trans (centralizer_le_normalizer _))
    · exact hc.trans ((center_le_centralizer (B : Set G)).trans (centralizer_le_normalizer _))
  · rintro rfl
    rfl

end Subgroup
