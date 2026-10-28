module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Marked four-groups in A₆

The standard four-group consists of the double transpositions on the first
four letters. The second lies in the same marked dihedral Sylow subgroup.
The genuine exceptional automorphism, followed by an explicit even relabelling,
interchanges their classes. Conjugating one involution to the marked central
involution reduces every four-group to these two cases.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570.
-/

@[expose] public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal.FourNormalizers
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 4096
abbrev V := Multiplicative (ZMod 2 × ZMod 2)
def standardEmbedding : V →* A6 where
  toFun i := dihedralRotation ^ (2 * i.toAdd.1.val) *
    (dihedralRotation * dihedralReflection) ^ i.toAdd.2.val
  map_one' := rfl
  map_mul' := by decide +kernel
def secondEmbedding : V →* A6 where
  toFun i := dihedralRotation ^ (2 * i.toAdd.1.val) *
    dihedralReflection ^ i.toAdd.2.val
  map_one' := rfl
  map_mul' := by decide +kernel
def standardFour : Subgroup A6 := standardEmbedding.range
def secondFour : Subgroup A6 := secondEmbedding.range
theorem standardEmbedding_injective : Function.Injective standardEmbedding := by decide +kernel
theorem secondEmbedding_injective : Function.Injective secondEmbedding := by decide +kernel
instance : IsKleinFour standardFour where
  card_four := (Nat.card_congr (MonoidHom.ofInjective standardEmbedding_injective).toEquiv).symm.trans (by simp)
  exponent_two := (Monoid.exponent_eq_of_mulEquiv (MonoidHom.ofInjective standardEmbedding_injective)).symm.trans (by simp)
instance : IsKleinFour secondFour where
  card_four := (Nat.card_congr (MonoidHom.ofInjective secondEmbedding_injective).toEquiv).symm.trans (by simp)
  exponent_two := (Monoid.exponent_eq_of_mulEquiv (MonoidHom.ofInjective secondEmbedding_injective)).symm.trans (by simp)
theorem mem_standardFour (x : A6) : x ∈ standardFour ↔ ∃ i, standardEmbedding i = x := Iff.rfl
theorem mem_secondFour (x : A6) : x ∈ secondFour ↔ ∃ i, secondEmbedding i = x := Iff.rfl

def tailSwap : Equiv.Perm (Fin 6) := Equiv.swap 4 5
noncomputable def classSwap : AutA6 :=
  permutationAction (Equiv.swap 1 2 * Equiv.swap 3 4) * outerAltAut

private theorem classSwap_values (i : V) :
    classSwap (standardEmbedding i) = secondEmbedding (.ofAdd (i.toAdd.1 + i.toAdd.2, i.toAdd.2)) := by
  apply Subtype.ext
  change (Equiv.swap 1 2 * Equiv.swap 3 4) * outerHom (standardEmbedding i).val *
    (Equiv.swap 1 2 * Equiv.swap 3 4)⁻¹ = _
  revert i
  decide +kernel

theorem classSwap_standardFour : standardFour.map classSwap.toMonoidHom = secondFour := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, (classSwap_values i).symm⟩
  · rintro _ ⟨i, rfl⟩
    have hi : ∃ j : V, Multiplicative.ofAdd (j.toAdd.1 + j.toAdd.2, j.toAdd.2) = i := by
      revert i
      decide +kernel
    obtain ⟨j, hj⟩ := hi
    exact ⟨_, ⟨j, rfl⟩, (classSwap_values j).trans (congrArg secondEmbedding hj)⟩

private theorem four_generators (F : Subgroup A6) [IsKleinFour F] :
    ∃ a b : A6, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧
      a * b = b * a ∧ ∀ x, x ∈ F ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  obtain ⟨f⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := V) (G₂ := F)
  let j : V →* A6 := F.subtype.comp f.toMonoidHom
  have hj : Function.Injective j := F.subtype_injective.comp f.injective
  let a₀ : V := .ofAdd (1, 0)
  let b₀ : V := .ofAdd (0, 1)
  refine ⟨j a₀, j b₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => (by decide : a₀ ≠ 1) (hj (h.trans j.map_one.symm))
  · exact fun h => (by decide : b₀ ≠ 1) (hj (h.trans j.map_one.symm))
  · exact fun h => (by decide : a₀ ≠ b₀) (hj h)
  · simpa only [map_pow, map_one] using congrArg j (show a₀ ^ 2 = 1 by decide)
  · simpa only [map_pow, map_one] using congrArg j (show b₀ ^ 2 = 1 by decide)
  · simpa only [map_mul] using congrArg j (show a₀ * b₀ = b₀ * a₀ by decide)
  · intro x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := f.surjective ⟨x, hx⟩
      have hxj : j t = x := congrArg Subtype.val ht
      rw [← hxj]
      have words : ∀ t : V, t = 1 ∨ t = a₀ ∨ t = b₀ ∨ t = a₀ * b₀ := by decide
      rcases words t with rfl | rfl | rfl | rfl
      · exact Or.inl j.map_one
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (j.map_mul _ _)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact F.one_mem
      · exact (f a₀).property
      · exact (f b₀).property
      · exact F.mul_mem (f a₀).property (f b₀).property

private theorem central_four_table (b : A6) (hb : b ≠ 1) (hab : dihedralRotation ^ 2 ≠ b)
    (hb2 : b ^ 2 = 1) (hc : dihedralRotation ^ 2 * b = b * dihedralRotation ^ 2) :
    (∀ x, (x = 1 ∨ x = dihedralRotation ^ 2 ∨ x = b ∨ x = dihedralRotation ^ 2 * b) ↔
      ∃ i, standardEmbedding i = x) ∨
    (∀ x, (x = 1 ∨ x = dihedralRotation ^ 2 ∨ x = b ∨ x = dihedralRotation ^ 2 * b) ↔
      ∃ i, secondEmbedding i = x) := by
  revert b
  decide +kernel

/-- Every four-group is carried to the marked one by an actual automorphism. -/
theorem exists_map_standardFour (F : Subgroup A6) [IsKleinFour F] :
    ∃ α : AutA6, standardFour.map α.toMonoidHom = F := by
  obtain ⟨a, b, ha, hb, hab, ha2, hb2, hc, hF⟩ := four_generators F
  have hz : orderOf (dihedralRotation ^ 2) = 2 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj a (dihedralRotation ^ 2)
    (orderOf_eq_prime ha2 ha) hz)
  let e := MulAut.conj g
  have hea : e a = dihedralRotation ^ 2 := hg
  have hmem (x : A6) : x ∈ F.map e.toMonoidHom ↔
      x = 1 ∨ x = dihedralRotation ^ 2 ∨ x = e b ∨ x = dihedralRotation ^ 2 * e b := by
    rw [mem_map_equiv, hF]
    simp only [e.symm_apply_eq, map_one, map_mul, hea]
  have hb' : e b ≠ 1 := by simpa using hb
  have hab' : dihedralRotation ^ 2 ≠ e b := by rw [← hea]; exact e.injective.ne hab
  have hb2' : (e b) ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have hc' : dihedralRotation ^ 2 * e b = e b * dihedralRotation ^ 2 := by
    rw [← hea, ← map_mul, hc, map_mul]
  rcases central_four_table (e b) hb' hab' hb2' hc' with h | h
  · have heq : F.map e.toMonoidHom = standardFour := by ext x; exact (hmem x).trans (h x)
    refine ⟨e.symm, ?_⟩
    rw [← heq, map_map]
    simp
  · have heq : F.map e.toMonoidHom = secondFour := by ext x; exact (hmem x).trans (h x)
    refine ⟨classSwap.trans e.symm, ?_⟩
    change standardFour.map (e.symm.toMonoidHom.comp classSwap.toMonoidHom) = F
    rw [← map_map, classSwap_standardFour, ← heq, map_map]
    simp
end AlternatingSix.ShadowLocal.FourNormalizers
