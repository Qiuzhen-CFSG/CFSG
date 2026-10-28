module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Sieve.Certificate
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage

/-!
# Sieve for the three admissible Rudvalis local centralizers

Every square-one element of the unchanged `localP` has a certified local
conjugator to one of sixteen words, including the identity. In thirteen cases,
checked words `x,y` centralize that representative, satisfy `x² = 1`, and fail
to commute with each other. The hypothesis that every square-one element of
the centralizer is central therefore leaves exactly the representatives at
indices 13, 37 and 158. All conjugators are the original local normal forms.

This proves the `RepresentativeCover` input to `LocalCentralizers` without
extra premises. In fact, the centralizer-order hypothesis is unnecessary for
this sieve. No ambient involution classification or group order is used.
Source motivation: GLS3 Table 5.3r and pp.291–292; Aschbacher–Smith I.2.2(7),
pp.412–413. The finite criterion itself is not asserted in those sources.
See `Sieve/source/README.md` for the untrusted witness discovery and provenance.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
open SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate

namespace Sieve

private theorem normalForm_conjugacy (n : Fin 16384) (hsq : normalForm n ^ 2 = 1) :
    ∃ (r : Fin 16) (g : Fin 16384),
      normalForm n = MulAut.conj (normalForm g) (normalForm (classIndex r)) := by
  let b : Fin 16 := ⟨n.val / 1024, by omega⟩
  let j : Fin 1024 := ⟨n.val % 1024, Nat.mod_lt _ (by decide)⟩
  have he : blockIndex b j = n := by
    apply Fin.ext
    dsimp [blockIndex, b, j]
    omega
  refine ⟨rowRep b j, rowConj b j, row_sound n _ _ ?_ hsq⟩
  exact he ▸ checkedBlock b j

private theorem class_is_good (r : Fin 16)
    (hc : CentralSquares (normalForm (classIndex r))) :
    ∃ s : Fin 3, normalForm (classIndex r) = representative s := by
  rcases badChecked r with h | h | h | h
  · subst r
    exact ⟨0, rfl⟩
  · subst r
    exact ⟨1, rfl⟩
  · subst r
    exact ⟨2, rfl⟩
  · exact (bad_sound r _ _ h hc).elim

end Sieve

/-- A square-one local element whose centralizer has central square-one
elements is locally conjugate to one of the three specified actual words. -/
public theorem representativeCover : RepresentativeCover := by
  intro i hi hsq _hcard hc
  obtain ⟨n, rfl⟩ := normalFormCover i hi
  obtain ⟨r, g, hg⟩ := Sieve.normalForm_conjugacy n hsq
  have hc' : Sieve.CentralSquares (normalForm (Sieve.classIndex r)) := by
    apply Sieve.centralSquares_of_conj (normalForm g) (normalForm_mem g)
    rw [← hg]
    exact hc
  obtain ⟨s, hs⟩ := Sieve.class_is_good r hc'
  exact ⟨s, normalForm g, normalForm_mem g,
    hg.trans (congrArg (MulAut.conj (normalForm g)) hs)⟩

end Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
