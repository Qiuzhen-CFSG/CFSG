module

public import Theory.SpecificGroups.ReeF4.SourceCompletion.InvolutionReduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses

/-!
# Exhaustion of the two involution classes in the native Ree model

The positive-subgroup coordinate argument proves that every nonidentity
involution in the actual positive Ree subgroup is conjugate to a nonzero long
or short root element. Sylow conjugacy places an arbitrary native involution
in that subgroup, and transports the resulting root-class witness back to the
original element. This is the native-model involution clause of
Aschbacher--Smith F.4.27(3), with the coordinates supplied by
Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8, internal
p.57.
-/

public noncomputable section
namespace ReeF4.SourceCompletion

open Subgroup Theory.GroupTheory Parabolics EvenInvolutionGeometry

/-- Every involution of the positive-parameter native Ree model lies in one
of its two actual root classes. -/
theorem involution_root_classes (m : ℕ) (hm : 1 ≤ m) (x : Model m)
    (hx : orderOf x = 2) :
    IsLongRootInvolution x ∨ IsShortRootInvolution x := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨U, hU⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  have hU' : (U : Subgroup (Model m)) = Parabolics.unipotent m :=
    hU.trans (MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent m)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model m) S U
  have hyU : (MulAut.conj g) x ∈ Parabolics.unipotent m := by
    rw [← hU', ← hg]
    exact ⟨x, hS (mem_zpowers x), rfl⟩
  have hy2 : ((MulAut.conj g) x) ^ 2 = 1 := by
    have hx2 : x ^ 2 = 1 := (orderOf_eq_prime_iff.mp hx).1
    rw [← map_pow, hx2, map_one]
  have hx_ne : x ≠ 1 := by
    intro h
    rw [h] at hx
    simp at hx
  have hy_ne : (MulAut.conj g) x ≠ 1 := by
    intro h
    apply hx_ne
    exact (MulAut.conj g).injective (by simpa only [h] using (map_one (MulAut.conj g)).symm)
  have hclasses :=
    (ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.unipotentRootCoverage
      m hm) ((MulAut.conj g) x) hyU hy_ne hy2
  have hxy : IsConj x ((MulAut.conj g) x) := isConj_iff.mpr ⟨g, rfl⟩
  rcases hclasses with hlong | hshort
  · obtain ⟨a, ha, hac⟩ := hlong
    exact Or.inl ⟨a, ha, hac.trans hxy.symm⟩
  · obtain ⟨a, ha, hac⟩ := hshort
    exact Or.inr ⟨a, ha, hac.trans hxy.symm⟩

end ReeF4.SourceCompletion
