module

public import Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTwoLocal
public import Theory.GroupTheory.CentralExtensionSwappedRankThree

/-!
# The swapped unitary tori exclude quasithin central covers

The coordinate swaps and prime tori constructed in `SwappedTori` lie in the
literal root normalizer or line parabolic. These subgroups are two-local.
The central-extension lifting theorem therefore gives an odd-prime rank-three
two-local subgroup in every finite central cover. No restriction on the order
of the central kernel is needed.

This supplies the concrete unitary input to Aschbacher--Smith A.2.18,
printed p.40. The five-dimensional argument uses a prime other than five.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
variable {F L : Type*} [Field F] [Finite F] [CharP F 2] [Group L] [Finite L]

/-- Every finite central cover is excluded by the literal root-normalizer torus. -/
theorem six_cover_not_quasithin (k : ℕ) (J : HermitianForm (6+k) F) (hJ : J.form = 1)
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center L) {q p : ℕ}
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q) (hconj : ∀ x, J.conj x = x ^ q)
    (hp : p.Prime) (ho : Odd p) (hd : p ∣ q + 1) : ¬ IsQuasithin L := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he, hs⟩ := six_swapped_embedding k J hJ hcard hq hconj hp hd
  exact CentralExtension.SwappedRankThree.not_quasithin f hf hk ho _
    (Theory.SpecificGroups.UnitaryRootNormalizer.rootNormalizer_isTwoLocal k J hJ) e he
    (by simpa only [CentralExtension.SwappedRankThree.basis_eq_mulSingle] using hs)

/-- The actual five-dimensional line parabolic excludes central covers when `p ≠ 5`. -/
theorem five_cover_not_quasithin (J : HermitianForm 5 F) (hJ : J.form = 1)
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center L) {q p : ℕ}
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q) (hconj : ∀ x, J.conj x = x ^ q)
    (hp : p.Prime) (ho : Odd p) (hd : p ∣ q + 1) (hne : p ≠ 5) : ¬ IsQuasithin L := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he, hs⟩ := five_swapped_embedding J hJ hcard hq hconj hp hd hne
  exact CentralExtension.SwappedRankThree.not_quasithin f hf hk ho _
    (Theory.SpecificGroups.UnitaryFive.lineParabolic_isTwoLocal J hJ) e he
    (by simpa only [CentralExtension.SwappedRankThree.basis_eq_mulSingle] using hs)

end Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
