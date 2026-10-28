module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Radical.Coordinates

/-!
# Coordinate transport for radical center candidates

The signed action of every permutation extends to an automorphism of the signed
A₆ extension by conjugating its actor. This preserves the sign subgroup and
both literal mixed coordinate equations. Multiplying a radical element by a
central sign or volume factor preserves its centralizer, so the normalization
in `Coordinates` applies to the original mixed candidate sets.

Source: Aschbacher–Smith, I.2.2(6a), printed pp.410 and 412, via the intrinsic
signed split extension; no ambient recognition assertion is used here.
-/

@[expose] public section
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions.Radical
open Equiv Subgroup

/-- Conjugation by a six-letter permutation preserves the alternating actor group. -/
def actorConj (p : Perm (Fin 6)) : A ≃* A where
  toFun a := ⟨p * a.val * p⁻¹, (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a.val a.property p⟩
  invFun a := ⟨p⁻¹ * a.val * p, by
    simpa using (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a.val a.property p⁻¹⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- The signed permutation automorphism on the actual semidirect product. -/
def transport (p : Perm (Fin 6)) : SplitExtension ≃* SplitExtension :=
  SemidirectProduct.congr (symmetricAction p) (actorConj p) (by
    intro a
    apply MulEquiv.ext
    intro m
    change symmetricAction p (symmetricAction a.val m) =
      symmetricAction (p * a.val * p⁻¹) (symmetricAction p m)
    simp only [← MulAut.mul_apply, ← map_mul]
    simp [mul_assoc])

private theorem transport_sign (p : Perm (Fin 6)) (x : SplitExtension) (hx : x ∈ sign) :
    transport p x ∈ sign := by
  rw [mem_sign_iff, mem_signKernel] at hx ⊢
  constructor
  · change permuteVector p x.left.vector = 0
    rw [hx.1]
    exact map_zero (BinaryPermutation.coreRepresentation (Fin 6) p)
  · change actorConj p x.right = 1
    rw [hx.2, map_one]

@[simp] private theorem transport_left (p : Perm (Fin 6)) (x : SplitExtension) :
    (transport p x).left = symmetricAction p x.left := rfl
@[simp] theorem transport_right (p : Perm (Fin 6)) (x : SplitExtension) :
    (transport p x).right = actorConj p x.right := rfl
@[simp] private theorem transport_vector (p : Perm (Fin 6)) (x : SplitExtension) :
    (transport p x).left.vector = permuteVector p x.left.vector := rfl
@[simp] private theorem transport_radical (p : Perm (Fin 6)) (m : Model) :
    transport p (radicalEmbedding m) =
      radicalEmbedding (symmetricAction p m) := by
  apply SemidirectProduct.ext
  · rfl
  · exact map_one (actorConj p)

/-- Transport preserves square admissibility and both mixed coordinate equations. -/
theorem transport_mixed (p : Perm (Fin 6)) (m : Model) (x y : SplitExtension)
    (hy : y ∈ mixedCandidates m x) :
    transport p y ∈ mixedCandidates (symmetricAction p m) (transport p x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow]
    exact transport_sign p _ hy.1
  · have hh := hy.2.1.map (transport p).toMonoidHom
    change Commute (transport p (radicalEmbedding m)) (transport p y) at hh
    rw [transport_radical] at hh
    exact hh
  · rw [← (transport p).map_mul x y, ← (transport p).map_mul y x]
    exact congrArg (actorConj p) hy.2.2.1
  · rw [← (transport p).map_mul x y, ← (transport p).map_mul y x]
    exact congrArg (permuteVector p) hy.2.2.2

private theorem center_of_vector (m : Model) (h : m.vector = 0 ∨ m.vector = volumeVector) :
    m ∈ center Model := by
  rcases h with h | h
  · exact signKernel_le_center ((mem_signKernel m).mpr h)
  · have he : m = centralSign m.sign * volume := by
      rw [centralSign_mul]
      exact Model.ext (by simp [volume]) h
    rw [he]
    exact (center Model).mul_mem (centralSign_mem_center _) Structure.volume_mem_center

private theorem commute_pair (m : Model)
    (h : m.vector = Structure.leftA.vector ∨
      m.vector = Structure.leftA.vector + volumeVector) (y : SplitExtension) :
    Commute (radicalEmbedding m) y ↔
      Commute (radicalEmbedding Structure.leftA) y := by
  have hs (v : V) : v + v = 0 := by
    apply Subtype.ext
    funext i
    exact CharTwo.add_self_eq_zero _
  have hz : m * Structure.leftA⁻¹ ∈ center Model := by
    apply center_of_vector
    rw [mul_vector, inv_vector]
    rcases h with h | h
    · exact Or.inl (h ▸ hs _)
    · right
      rw [h, add_right_comm, hs, zero_add]
  have hc : Commute (radicalEmbedding (m * Structure.leftA⁻¹)) y :=
    (mem_center_iff.mp (central_le_center ⟨_, hz, rfl⟩) y).symm
  constructor
  · intro hmy
    have hh := hc.inv_left.mul_left hmy
    simpa only [map_mul, map_inv, mul_inv_rev, inv_inv, inv_mul_cancel_right] using hh
  · intro hmy
    have hh := hc.mul_left hmy
    simpa only [map_mul, map_inv, inv_mul_cancel_right] using hh

/-- Normalization supplies an actual automorphism and the original pair centralizer. -/
theorem exists_normalized_centralizer (m : Model) (hm : m ∉ center Model) :
    ∃ p : Perm (Fin 6), ∀ y : SplitExtension,
      Commute (radicalEmbedding (symmetricAction p m)) y ↔
        Commute (radicalEmbedding Structure.leftA) y := by
  have h0 : m.vector ≠ 0 := fun h => hm (center_of_vector m (Or.inl h))
  have hvol : m.vector ≠ volumeVector := fun h => hm (center_of_vector m (Or.inr h))
  obtain ⟨p, hp⟩ := exists_normalization m.vector h0 hvol
  exact ⟨p, fun y => commute_pair (symmetricAction p m) hp y⟩

end EvenCliffordSix.SplitExtension.ElementaryRestrictions.Radical
