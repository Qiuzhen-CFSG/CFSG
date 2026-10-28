module

public import Theory.SpecificGroups.Suzuki.NonsplitTori
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups

/-!
# Standard containment for Suzuki subgroups

The four standard alternatives are containment, after conjugation, in the
Borel or in one of the three torus normalizers. A subgroup normalizing a
nontrivial subgroup of a partition member satisfies these alternatives:
partition uniqueness first forces it to normalize the whole member.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e).
-/

namespace BenderSuzuki.MatrixGroups

/-- The four standard solvable alternatives in the Suzuki subgroup theorem. -/
@[expose] public def SuzukiStandardContainment {m : ℕ} (T : SuzukiNonsplitTorusPair m)
    (H : Subgroup (SuzukiMatrixGroup m)) : Prop :=
  ∃ g, H.map (MulAut.conj g).toMonoidHom ≤ SuzukiBorelSubgroup m ∨
    H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) ∨
    H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (T.plus : Set (SuzukiMatrixGroup m)) ∨
    H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (T.minus : Set (SuzukiMatrixGroup m))

/-- Standard containment passes to subgroups. -/
public theorem SuzukiStandardContainment.mono {m : ℕ} {T : SuzukiNonsplitTorusPair m}
    {H K : Subgroup (SuzukiMatrixGroup m)} (hK : SuzukiStandardContainment T K)
    (hHK : H ≤ K) : SuzukiStandardContainment T H := by
  obtain ⟨g, h | h | h | h⟩ := hK
  · exact ⟨g, Or.inl ((Subgroup.map_mono hHK).trans h)⟩
  · exact ⟨g, Or.inr (Or.inl ((Subgroup.map_mono hHK).trans h))⟩
  · exact ⟨g, Or.inr (Or.inr (Or.inl ((Subgroup.map_mono hHK).trans h)))⟩
  · exact ⟨g, Or.inr (Or.inr (Or.inr ((Subgroup.map_mono hHK).trans h)))⟩

/-- The trivial subgroup satisfies standard containment. -/
public theorem suzukiStandardContainment_bot {m : ℕ} (T : SuzukiNonsplitTorusPair m) :
    SuzukiStandardContainment T ⊥ :=
  ⟨1, Or.inl (by rw [Subgroup.map_bot]; exact bot_le)⟩

private theorem conjugate_le_of_le_conjugate {G : Type*} [Group G]
    (H K : Subgroup G) (g : G) (h : H ≤ K.map (MulAut.conj g).toMonoidHom) :
    H.map (MulAut.conj g⁻¹).toMonoidHom ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := h hx
  simpa [MulAut.conj_apply, mul_assoc] using hy

/-- The normalizer of each partition member is a standard alternative. -/
public theorem suzukiStandardContainment_of_le_partition_normalizer {m : ℕ}
    (hm : 0 < m) (T : SuzukiNonsplitTorusPair m)
    {H U : Subgroup (SuzukiMatrixGroup m)} (hU : SuzukiPartitionMember m U)
    (hH : H ≤ Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) :
    SuzukiStandardContainment T H := by
  have hconj (V : Subgroup (SuzukiMatrixGroup m)) (g : SuzukiMatrixGroup m)
      (h : U = V.map (MulAut.conj g).toMonoidHom) :
      H.map (MulAut.conj g⁻¹).toMonoidHom ≤
        Subgroup.normalizer (V : Set (SuzukiMatrixGroup m)) := by
    apply conjugate_le_of_le_conjugate H _ g
    rwa [Subgroup.map_normalizer_eq_of_bijective V (MulAut.conj g).bijective, ← h]
  rcases (suzukiPartitionMember_iff m U).mp hU with ⟨g, hg⟩ | ⟨g, hg⟩ | hU
  · exact ⟨g⁻¹, Or.inl (by
      simpa only [suzukiRootSubgroup_normalizer m hm] using hconj _ g hg)⟩
  · exact ⟨g⁻¹, Or.inr (Or.inl (hconj _ g hg))⟩
  · rcases T.covers U hU with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact ⟨g⁻¹, Or.inr (Or.inr (Or.inl (hconj _ g hg)))⟩
    · exact ⟨g⁻¹, Or.inr (Or.inr (Or.inr (hconj _ g hg)))⟩

/-- A nontrivial normalized subgroup lying in a partition member forces
standard containment of its normalizing group. -/
public theorem suzukiStandardContainment_of_normal_partition_subgroup {m : ℕ}
    (hm : 0 < m) (T : SuzukiNonsplitTorusPair m)
    {H A U : Subgroup (SuzukiMatrixGroup m)} (hA : A ≠ ⊥)
    (hAU : A ≤ U) (hU : SuzukiPartitionMember m U)
    (hH : H ≤ Subgroup.normalizer (A : Set (SuzukiMatrixGroup m))) :
    SuzukiStandardContainment T H :=
  suzukiStandardContainment_of_le_partition_normalizer hm T hU
    (hH.trans (hU.normalizer_le hm hAU hA))

end BenderSuzuki.MatrixGroups
