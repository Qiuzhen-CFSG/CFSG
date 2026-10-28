module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.Geometry
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.SingerExclusion
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Normalization
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.LinearFrame
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.GramDiagonal

/-!
# Invariant orthogonal frames for nonabelian odd special-unitary subgroups

The linear-frame construction supplies three independent projective lines
over the original finite field, preserved by the odd subgroup H and its given
normalizing involution t. Nonabelianness of H forces their Gram matrix to be
diagonal. Finite-field norm surjectivity normalizes these same lines to an
orthonormal basis, preserving the whole join H⟨t⟩.

This proves the nonabelian geometric branch of Lemma 3.11(a), with no extra
linear-frame, orthogonality or three-core premise. The resulting setwise
stabilizer normalizes the literal special-unitary frame torus. The abelian and
projective branches and the numerical torus conclusions are assembled elsewhere.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

/-- The nonabelian odd subgroup and its given normalizing involution preserve
an orthonormal frame over the original field. This is the nonabelian geometric
branch of GLS4, Chapter 4, Lemma 3.11(a). -/
theorem special_frame_of_nonabelian [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (hna : ¬ IsMulCommutative H) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ specialFrameStabilizer J P := by
  obtain ⟨C, hC⟩ := NonabelianFrame.exists_preserved_linear_frame
    J n hn hcard hfixed H hodd hna t ht htH hB
  exact NonabelianFrame.specialFrameStabilizer_of_nonabelian_odd_preservesLines
    J (2 ^ n) hcard hfixed H (H ⊔ zpowers t) le_sup_left hodd hna C hC

/-- The nonabelian source branch places the whole join in the normalizer of
the actual special-unitary frame torus constructed from its orthonormal basis. -/
theorem special_placement_of_nonabelian [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (hna : ¬ IsMulCommutative H) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P) := by
  obtain ⟨P, hP⟩ := special_frame_of_nonabelian J n hn hcard hfixed H hodd hna t ht htH hB
  exact ⟨P, hP.trans (specialFrameStabilizer_le_normalizer J P)⟩

end UnitaryThree.OddTorusNormalizer
