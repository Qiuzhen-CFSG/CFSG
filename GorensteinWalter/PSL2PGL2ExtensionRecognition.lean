module
public import GorensteinWalter.NormalPSL2IndexTwoPGL

/-!
# Recognition of a PSL₂/PGL₂ extension

A finite group with a normal actual `PSL₂(E)` subgroup of index one or two is
recognized as the corresponding actual projective model.  The index-one case
is the subgroup itself, while the index-two case uses the established
Gorenstein--Walter extension recognizer.  The field remains an explicit odd
prime-power field, so the statement includes `|E| = 3`, `5`, and `9` without
special exclusions.  This is the extension-recognition step used after
intersecting a subgroup of `PGL₂` with its canonical `PSL₂` layer.
-/

namespace GorensteinWalter
universe u

/-- Recognize a finite `PSL₂(E)` extension whose normal core has index one or two. -/
public theorem exists_mulEquiv_psl2_or_pgl2_of_normal_psl2_index_one_or_two
    {A : Type u} [Group A] [Finite A]
    (hAd : HasDihedralSylowTwo A)
    (E : Type u) [Field E] [Finite E]
    (hE : IsOddPrimePower (Nat.card E))
    (N : Subgroup A) [N.Normal] (eN : N ≃* PSL2 E)
    (hidx : N.index = 1 ∨ N.index = 2) :
    Nonempty (A ≃* PSL2 E) ∨ Nonempty (A ≃* PGL2 E) := by
  rcases hidx with hone | htwo
  · left
    have htop : N = ⊤ := Subgroup.index_eq_one.mp hone
    exact ⟨(Subgroup.topEquiv.symm.trans
      (MulEquiv.subgroupCongr htop.symm)).trans eN⟩
  · right
    exact ⟨(exists_mulEquiv_pgl2_of_normal_psl2_index_two
      hAd N htwo E hE eN).choose⟩

end GorensteinWalter
