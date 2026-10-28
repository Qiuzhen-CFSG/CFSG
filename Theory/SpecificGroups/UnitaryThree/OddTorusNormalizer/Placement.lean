module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.Geometry
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.ProjectiveLift
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame

/-!
# Odd-subgroup placement in unitary frame-torus normalizers

An odd subgroup of SU₃, normalized by an involution and contained in no
isotropic-line stabilizer, preserves an orthonormal frame together with that
involution. The abelian and nonabelian constructions cover all such subgroups.
The full preimage and a genuine involution lift give the same conclusion in
PSU₃. Setwise frame stabilizers normalize the published literal frame tori.

The final placement theorems discharge frame existence for both actual
carriers under the field-cardinality and no-Borel hypotheses of GLS4,
Chapter 4, Lemma 3.11(a). Borels use their geometric convention as stabilizers
of isotropic projective lines. Numerical torus structure and the remaining
clauses of that lemma are assembled separately.

Source: `refs/KGroup/GLS4/Chapter4.tex`, lines 585–603; application in
Chapter 2 Lemma 17.4, `refs/KGroup/GLS4/Chapter2.tex`, lines 3136–3147.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

/-- A concrete preserved orthogonal frame gives special-unitary torus placement. -/
theorem special_placement_of_frame (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (t : J.specialSubgroup) (P : OrthogonalFrame J)
    (hP : H ⊔ zpowers t ≤ specialFrameStabilizer J P) :
    H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P) :=
  hP.trans (specialFrameStabilizer_le_normalizer J P)

/-- The same geometric witness gives placement in the literal projective torus normalizer. -/
theorem projective_placement_of_frame (J : HermitianForm 3 E)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (P : OrthogonalFrame J)
    (hP : H ⊔ zpowers t ≤ projectiveFrameStabilizer J P) :
    H ⊔ zpowers t ≤ normalizer (projectiveFrameTorus J P) :=
  hP.trans (projectiveFrameStabilizer_le_normalizer J P)

/-- Actual PSU₃ placement from the SU₃ frame construction, retaining the odd
scalar kernel and discharging all quotient-lifting hypotheses. -/
theorem projective_placement_of_special_frames [Finite E] (J : HermitianForm 3 E)
    (hspecial : ∀ (H : Subgroup J.specialSubgroup), Odd (Nat.card H) →
      ∀ t : J.specialSubgroup, orderOf t = 2 → t ∈ normalizer H →
        SpecialNoBorel J H → ∃ P : OrthogonalFrame J,
          H ⊔ zpowers t ≤ specialFrameStabilizer J P)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hH : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ normalizer (projectiveFrameTorus J P) := by
  obtain ⟨P, hP⟩ := projective_frame_of_special_frames J hspecial H hH t ht htH hB
  exact ⟨P, projective_placement_of_frame J H t P hP⟩

/-- Every odd special-unitary subgroup excluded from the Borels and normalized
by an involution preserves an orthonormal frame together with that involution.
The abelian and nonabelian constructions exhaust the source hypotheses. -/
theorem special_frame_of_odd [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ specialFrameStabilizer J P := by
  by_cases hcomm : IsMulCommutative H
  · let : IsMulCommutative H := hcomm
    exact special_frame_of_abelian J hn hcard hfixed H hodd t ht htH hB
  · exact special_frame_of_nonabelian J n hn hcard hfixed H hodd hcomm t ht htH hB

/-- Frame existence descends through the actual SU₃-to-PSU₃ map, retaining
the full odd preimage and lifting the specified projective involution. -/
theorem projective_frame_of_odd [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ projectiveFrameStabilizer J P :=
  projective_frame_of_special_frames J (special_frame_of_odd J hn hcard hfixed)
    H hodd t ht htH hB

/-- GLS4, Chapter 4, Lemma 3.11(a), for the actual SU₃ carrier: an odd
subgroup outside every Borel and its normalizing involution lie in the
normalizer of a torus diagonal in an orthonormal basis over the original field. -/
theorem special_placement [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P) := by
  obtain ⟨P, hP⟩ := special_frame_of_odd J hn hcard hfixed H hodd t ht htH hB
  exact ⟨P, special_placement_of_frame J H t P hP⟩

/-- GLS4, Chapter 4, Lemma 3.11(a), for the actual PSU₃ carrier, with its
torus the literal image of the special-unitary frame torus. -/
theorem projective_placement [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ zpowers t ≤ normalizer (projectiveFrameTorus J P) := by
  obtain ⟨P, hP⟩ := projective_frame_of_odd J hn hcard hfixed H hodd t ht htH hB
  exact ⟨P, projective_placement_of_frame J H t P hP⟩

end UnitaryThree.OddTorusNormalizer
