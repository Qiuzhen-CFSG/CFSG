module

public import Theory.SpecificGroups.Thompson.Model.Order.Subgroup
public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.GroupTheory.Index

/-!
# Coset certificates for the concrete Thompson subgroup

The index count splits into independent upper and lower bounds. A generator
coset cover gives the upper bound by induction on words in the two certified
ambient generators. A family of distinct right cosets gives the lower bound
by injectivity of multiplication from the subgroup times the family. Cancelling
the positive, but unknown, subgroup cardinality proves both index bounds.
The two families need not use the same representatives.

These are certificate-consumption theorems, not a construction of the
143127000 cosets. The concrete cover and separation certificates remain to be
proved. In particular, no ambient order or local subgroup order is assumed.

Source of the candidate index and subgroup words:
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/ThG1-max1W1 .
The counting argument is the usual coset partition argument; the source page
does not supply its required certificates.
-/

namespace Thompson.OrderCertificate

/-- The two certified generators, indexed for `GeneratorCosetCover`. -/
@[expose] public def cosetGenerators : Bool → Model
  | false => generatorA
  | true => generatorB

public theorem cosetGenerators_generate :
    Subgroup.closure (Set.range cosetGenerators) = ⊤ := by
  have hr : Set.range cosetGenerators = {generatorA, generatorB} := by
    ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [cosetGenerators]
    · rintro (rfl | rfl)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  rw [hr]
  exact closure_generators

/-- A finite certified covering bounds the index without knowing either order. -/
public theorem localSubgroup_index_le_of_cover {ι : Type*} [Finite ι]
    (C : Subgroup.GeneratorCosetCover localSubgroup cosetGenerators ι) :
    localSubgroup.index ≤ Nat.card ι := by
  have h := (C.finite_card_le cosetGenerators_generate).2
  rw [← localSubgroup.card_mul_index] at h
  exact Nat.le_of_mul_le_mul_left h Nat.card_pos

/-- Distinct right cosets bound the index independently of any covering. -/
public theorem localSubgroup_index_ge_of_separated {ι : Type*} [Finite ι]
    (repr : ι → Model)
    (separate : ∀ i j, repr i * (repr j)⁻¹ ∈ localSubgroup → i = j) :
    Nat.card ι ≤ localSubgroup.index := by
  let f : localSubgroup × ι → Model := fun p => p.1.val * repr p.2
  have hinj : Function.Injective f := by
    rintro ⟨h, i⟩ ⟨k, j⟩ he
    change h.val * repr i = k.val * repr j at he
    have hij : i = j := by
      apply separate
      have hr : repr i * (repr j)⁻¹ = h.val⁻¹ * k.val := by
        calc
          repr i * (repr j)⁻¹ =
              h.val⁻¹ * (h.val * repr i) * (repr j)⁻¹ := by simp
          _ = h.val⁻¹ * (k.val * repr j) * (repr j)⁻¹ := by rw [he]
          _ = h.val⁻¹ * k.val := by simp [mul_assoc]
      rw [hr]
      exact localSubgroup.mul_mem (localSubgroup.inv_mem h.property) k.property
    subst j
    exact Prod.ext (Subtype.ext (mul_right_cancel he)) rfl
  have h := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, ← localSubgroup.card_mul_index] at h
  exact Nat.le_of_mul_le_mul_left h Nat.card_pos

/-- Fixing the two concrete subgroup generators bounds any orbit by the index.
An action used here must be an action of the fixed matrix carrier. -/
public theorem localSubgroup_orbit_card_le_index {X : Type*} [MulAction Model X]
    (x : X) (ha : localA • x = x) (hb : localB • x = x) :
    (MulAction.orbit Model x).ncard ≤ localSubgroup.index := by
  have hle : localSubgroup ≤ MulAction.stabilizer Model x := by
    change Subgroup.closure {localA, localB} ≤ _
    apply (Subgroup.closure_le _).2
    intro g hg
    rcases hg with rfl | hg
    · exact ha
    · obtain rfl : g = localB := hg
      exact hb
  rw [← MulAction.index_stabilizer]
  exact Subgroup.index_antitone hle

end Thompson.OrderCertificate
