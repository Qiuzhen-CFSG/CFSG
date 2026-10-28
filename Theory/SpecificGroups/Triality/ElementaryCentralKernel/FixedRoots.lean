module

public import Theory.SpecificGroups.Triality.RootGeometryBasic
public import Theory.SpecificGroups.Triality.LeviArmCommutation

/-!
# Fixed root elements in the elementary triality group

The signed central-vertex curves with q-Frobenius fixed parameters and the
three-arm products with parameters `(t,F(t),F²(t))` are actual graph-field
fixed points. Orthogonality of the arms and the characteristic-power identities
show that these products are killed by the characteristic prime. Consequently
both signs belong to the elementary fixed-point subgroup, including q = 2.

The elementary center therefore centralizes these explicit split matrices.
This establishes the input to a matrix-centralizer comparison; it does not
assert that the fixed roots generate all fixed points or identify the
center of the elementary group with the center of the split group.

Source: GLS3 §2.4 root parametrizations, Theorem 2.2.6, and the central-kernel
paragraph in the proof of 2.3.4–5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.ElementaryCentralKernel
open Parabolics
noncomputable section

/-- A signed pinned simple-root curve; `true` is positive. -/
def simpleRoot (P : Parameters) (s : Bool) (i : Fin 4) (t : ExtensionField P) :
    SplitGroup P := if s then positiveRoot P i t else negativeRoot P i t

lemma simpleRoot_pow_prime (P : Parameters) (s : Bool) (i : Fin 4)
    (t : ExtensionField P) : simpleRoot P s i t ^ P.prime = 1 := by
  cases s
  · exact negativeRoot_pow_prime P i t
  · exact positiveRoot_pow_prime P i t

lemma graphField_simpleRoot (P : Parameters) (s : Bool) (i : Fin 4)
    (t : ExtensionField P) :
    graphFieldAutomorphism P (simpleRoot P s i t) =
      simpleRoot P s (typeD4DiagramPermutation i) (fieldFrobenius P t) := by
  cases s
  · exact graphField_negativeRoot P i t
  · exact graphField_positiveRoot P i t

lemma commute_arm_simpleRoot (P : Parameters) (hp : P.prime = 2) (s : Bool)
    (i j : Fin 4) (hi : i ≠ 1) (hj : j ≠ 1) (hij : i ≠ j)
    (t u : ExtensionField P) :
    Commute (simpleRoot P s i t) (simpleRoot P s j u) := by
  cases s
  · exact (armRootCommutation P hp).negative_negative i j hi hj hij t u
  · exact (armRootCommutation P hp).positive_positive i j hi hj hij t u

/-- The actual three-arm root product, with graph-field compatible parameters. -/
def foldedRoot (P : Parameters) (s : Bool) (t : ExtensionField P) : SplitGroup P :=
  simpleRoot P s 0 t * simpleRoot P s 2 (fieldFrobenius P t) *
    simpleRoot P s 3 (fieldFrobenius P (fieldFrobenius P t))

lemma graphField_foldedRoot (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (t : ExtensionField P) :
    graphFieldAutomorphism P (foldedRoot P s t) = foldedRoot P s t := by
  simp only [foldedRoot, map_mul, graphField_simpleRoot, fieldFrobenius_three]
  change simpleRoot P s 2 (fieldFrobenius P t) *
    simpleRoot P s 3 (fieldFrobenius P (fieldFrobenius P t)) * simpleRoot P s 0 t = _
  exact ((commute_arm_simpleRoot P hp s 0 2 (by decide) (by decide) (by decide) _ _).mul_right
    (commute_arm_simpleRoot P hp s 0 3 (by decide) (by decide) (by decide) _ _)).symm.eq.trans
      (mul_assoc _ _ _).symm

lemma foldedRoot_pow_prime (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (t : ExtensionField P) : foldedRoot P s t ^ P.prime = 1 := by
  unfold foldedRoot
  rw [((commute_arm_simpleRoot P hp s 0 3 (by decide) (by decide) (by decide) _ _).mul_left
    (commute_arm_simpleRoot P hp s 2 3 (by decide) (by decide) (by decide) _ _)).mul_pow,
    (commute_arm_simpleRoot P hp s 0 2 (by decide) (by decide) (by decide) _ _).mul_pow]
  simp only [simpleRoot_pow_prime, one_mul]

/-- The central-vertex curve lifts to elementary fixed points when its
parameter is fixed by q-Frobenius. -/
def centralElementary (P : Parameters) (s : Bool) (t : ExtensionField P)
    (ht : fieldFrobenius P t = t) : ElementaryGroup P := by
  let g : fixedSubgroup P := ⟨simpleRoot P s 1 t, by
    rw [mem_fixedSubgroup, graphField_simpleRoot, ht]
    rfl⟩
  exact ⟨g, mem_elementarySubgroup_of_pow P g 1 (by
    apply Subtype.ext
    change simpleRoot P s 1 t ^ (P.prime ^ 1) = 1
    rw [pow_one]
    exact simpleRoot_pow_prime P s 1 t)⟩

/-- Both signs of the folded root lift to the actual elementary subgroup. -/
def foldedElementary (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (t : ExtensionField P) : ElementaryGroup P := by
  let g : fixedSubgroup P := ⟨foldedRoot P s t, graphField_foldedRoot P hp s t⟩
  exact ⟨g, mem_elementarySubgroup_of_pow P g 1 (by
    apply Subtype.ext
    change foldedRoot P s t ^ (P.prime ^ 1) = 1
    rw [pow_one]
    exact foldedRoot_pow_prime P hp s t)⟩

@[simp] lemma elementaryInclusion_centralElementary (P : Parameters) (s : Bool)
    (t : ExtensionField P) (ht : fieldFrobenius P t = t) :
    elementaryInclusion P (centralElementary P s t ht) = simpleRoot P s 1 t := rfl

@[simp] lemma elementaryInclusion_foldedElementary (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (t : ExtensionField P) :
    elementaryInclusion P (foldedElementary P hp s t) = foldedRoot P s t := rfl

/-- Explicit matrices whose centralizer contains the image of the elementary
center. This is a set of genuine fixed root elements, not a generation premise. -/
def fixedRootGenerators (P : Parameters) : Set (SplitGroup P) :=
  {g | (∃ s t, fieldFrobenius P t = t ∧ g = simpleRoot P s 1 t) ∨
    ∃ s t, g = foldedRoot P s t}

lemma fixedRootGenerators_le_elementaryRange (P : Parameters) (hp : P.prime = 2) :
    fixedRootGenerators P ⊆ (elementaryInclusion P).range := by
  rintro g (⟨s, t, ht, rfl⟩ | ⟨s, t, rfl⟩)
  · exact ⟨centralElementary P s t ht, rfl⟩
  · exact ⟨foldedElementary P hp s t, rfl⟩

private lemma center_le_centralizer_comap {A B : Type*} [Group A] [Group B]
    (f : A →* B) (S : Set B) (hS : S ⊆ f.range) :
    Subgroup.center A ≤ (Subgroup.centralizer S).comap f := by
  intro z hz
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨x, rfl⟩ := hS hg
  simpa only [map_mul] using congrArg f ((Subgroup.mem_center_iff.mp hz) x)

/-- Centrality in the elementary group implies the concrete fixed-root
commutation equations in the split matrix group. -/
lemma elementaryCenter_le_fixedRootCentralizer (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (ElementaryGroup P) ≤
      (Subgroup.centralizer (fixedRootGenerators P)).comap (elementaryInclusion P) :=
  center_le_centralizer_comap (elementaryInclusion P) (fixedRootGenerators P)
    (fixedRootGenerators_le_elementaryRange P hp)

/-- The cubic coefficient extension contains a nontrivial Frobenius orbit. -/
theorem exists_frobenius_moved (P : Parameters) :
    ∃ t : ExtensionField P, fieldFrobenius P t ≠ t := by
  by_contra h
  have hall : ∀ t : ExtensionField P, fieldFrobenius P t = t := by
    simpa only [not_exists, not_not] using h
  have hbij : Function.Bijective (fixedField P).subtype :=
    ⟨(fixedField P).subtype_injective, fun t => ⟨⟨t, hall t⟩, rfl⟩⟩
  have hcard := Nat.card_congr (Equiv.ofBijective (fixedField P).subtype hbij)
  rw [card_fixedField, card_extensionField] at hcard
  have hlt : P.q ^ 1 < P.q ^ 3 :=
    Nat.pow_lt_pow_right (by have := P.q_ge_two; omega) (by decide)
  rw [pow_one, ← hcard] at hlt
  exact (lt_irrefl _ hlt)

/-- A nontrivial orbit of an automorphism of order dividing three has three
distinct parameters. This includes the cubic extension of the binary field. -/
theorem frobenius_orbit_pairwise (P : Parameters) (t : ExtensionField P)
    (ht : fieldFrobenius P t ≠ t) :
    t ≠ fieldFrobenius P t ∧
      t ≠ fieldFrobenius P (fieldFrobenius P t) ∧
      fieldFrobenius P t ≠ fieldFrobenius P (fieldFrobenius P t) := by
  refine ⟨Ne.symm ht, ?_, ?_⟩
  · intro h
    have he := congrArg (fieldFrobenius P) h
    rw [fieldFrobenius_three] at he
    exact ht he
  · intro h
    exact ht ((fieldFrobenius P).injective h).symm

end
end Triality.Standard.ElementaryCentralKernel
