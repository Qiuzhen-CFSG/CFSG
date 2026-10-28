module

public import Theory.SpecificGroups.Suzuki.BorelSolvable
public import Theory.SpecificGroups.Suzuki.NonsplitTori
public import Theory.SpecificGroups.DihedralSolvable
public import Theory.GroupTheory.SolvableConjugate

/-!
# The solvable subgroup alternatives for Suzuki groups

For `m > 0`, the standard Borel, the split-torus normalizer and the two
nonsplit-torus normalizers in `Sz(2^(2m+1))` are solvable. The Borel is a
solvable root-by-torus extension, the split normalizer is dihedral, and
each nonsplit normalizer is cyclic-by-cyclic. The latter argument only
needs cyclicity of the quotient, not its exact order four.

Solvability transfers to every subgroup conjugate into any of these four
groups. The final theorem packages this implication in the form used by
subgroup recognition. It does not assume the subgroup classification.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10 and XI.3.12(e),
printed pp. 190--194.
-/

namespace BenderSuzuki.MatrixGroups

/-- The normalizer of the standard split torus is solvable. -/
public theorem suzukiSplitTorus_normalizer_isSolvable (m : ℕ) (hm : 0 < m) :
    Group.IsSolvable
      (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))) := by
  obtain ⟨e⟩ := suzukiSplitTorus_normalizer_dihedral m hm
  let := GLS3.Chapter5.dihedralGroup_isSolvable (2 ^ (2 * m + 1) - 1)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- A maximal nonsplit torus has solvable normalizer: both the torus and
the normalizer quotient are cyclic. -/
public theorem IsSuzukiMaximalNonsplit.normalizer_isSolvable
    {m : ℕ} (hm : 0 < m) {U : Subgroup (SuzukiMatrixGroup m)}
    (hU : IsSuzukiMaximalNonsplit m U) :
    Group.IsSolvable (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) := by
  let N := Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))
  let V := U.subgroupOf N
  let : IsCyclic U := hU.isCyclic hm
  let := IsCyclic.commGroup (α := U)
  let e := Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := U))
  let : Group.IsSolvable V :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : IsCyclic (N ⧸ V) := (hU.normalizer_quotient hm).1
  let := IsCyclic.commGroup (α := N ⧸ V)
  exact (Group.isSolvable_iff_subgroup_quotient V).mpr ⟨inferInstance, inferInstance⟩

/-- The normalizer of the torus of order `q + 2r + 1` is solvable. -/
public theorem SuzukiNonsplitTorusPair.plus_normalizer_isSolvable
    {m : ℕ} (hm : 0 < m) (T : SuzukiNonsplitTorusPair m) :
    Group.IsSolvable (Subgroup.normalizer (T.plus : Set (SuzukiMatrixGroup m))) :=
  T.plus_maximal.normalizer_isSolvable hm

/-- The normalizer of the torus of order `q - 2r + 1` is solvable. -/
public theorem SuzukiNonsplitTorusPair.minus_normalizer_isSolvable
    {m : ℕ} (hm : 0 < m) (T : SuzukiNonsplitTorusPair m) :
    Group.IsSolvable (Subgroup.normalizer (T.minus : Set (SuzukiMatrixGroup m))) :=
  T.minus_maximal.normalizer_isSolvable hm

/-- A subgroup conjugate into the standard Borel is solvable. -/
public theorem suzukiSubgroup_isSolvable_of_conjugate_le_borel
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (h : ∃ g, H.map (MulAut.conj g).toMonoidHom ≤ SuzukiBorelSubgroup m) :
    Group.IsSolvable H := by
  obtain ⟨g, hg⟩ := h
  let := suzukiBorelSubgroup_isSolvable m hm
  exact Group.isSolvable_of_conjugate_le H (SuzukiBorelSubgroup m) g hg

/-- A subgroup conjugate into the split-torus normalizer is solvable. -/
public theorem suzukiSubgroup_isSolvable_of_conjugate_le_split_normalizer
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (h : ∃ g, H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))) :
    Group.IsSolvable H := by
  obtain ⟨g, hg⟩ := h
  let := suzukiSplitTorus_normalizer_isSolvable m hm
  exact Group.isSolvable_of_conjugate_le H _ g hg

/-- A subgroup conjugate into a maximal nonsplit-torus normalizer is solvable. -/
public theorem IsSuzukiMaximalNonsplit.isSolvable_of_conjugate_le_normalizer
    {m : ℕ} (hm : 0 < m) {U : Subgroup (SuzukiMatrixGroup m)}
    (hU : IsSuzukiMaximalNonsplit m U) (H : Subgroup (SuzukiMatrixGroup m))
    (h : ∃ g, H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) : Group.IsSolvable H := by
  obtain ⟨g, hg⟩ := h
  let := hU.normalizer_isSolvable hm
  exact Group.isSolvable_of_conjugate_le H _ g hg

/-- Each of the four non-subfield alternatives in XI.3.12(e) is solvable,
including all subgroups conjugate into one of them. -/
public theorem SuzukiNonsplitTorusPair.isSolvable_of_conjugate_le_alternative
    {m : ℕ} (hm : 0 < m) (T : SuzukiNonsplitTorusPair m)
    (H : Subgroup (SuzukiMatrixGroup m))
    (h : ∃ g, H.map (MulAut.conj g).toMonoidHom ≤ SuzukiBorelSubgroup m ∨
      H.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) ∨
      H.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (T.plus : Set (SuzukiMatrixGroup m)) ∨
      H.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (T.minus : Set (SuzukiMatrixGroup m))) :
    Group.IsSolvable H := by
  obtain ⟨g, hg | hg | hg | hg⟩ := h
  · exact suzukiSubgroup_isSolvable_of_conjugate_le_borel hm H ⟨g, hg⟩
  · exact suzukiSubgroup_isSolvable_of_conjugate_le_split_normalizer hm H ⟨g, hg⟩
  · exact T.plus_maximal.isSolvable_of_conjugate_le_normalizer hm H ⟨g, hg⟩
  · exact T.minus_maximal.isSolvable_of_conjugate_le_normalizer hm H ⟨g, hg⟩

end BenderSuzuki.MatrixGroups
