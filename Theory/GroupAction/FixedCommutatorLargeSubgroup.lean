module

public import Theory.GroupAction.FixedDisplacementIndexTwo
public import Theory.GroupTheory.SubgroupConjugation

/-!
# A large subgroup with involution commutator in one layer

Suppose K normalizes an abelian subgroup U containing R, an order-two Z,
and an element t of square one. If K centralizes R joined with Z and its
commutator with t's cyclic group lies there, then K has a subgroup of at
least half its order whose entire commutator with that cyclic group lies in R.
The subgroup is returned in the original ambient group.

Use the actual conjugation action of K on U. The native quotient of R joined
with Z by R has order at most two. The fixed-displacement kernel construction
therefore yields a native subgroup of K of index at most two. Map it into the
ambient group. The cyclic subgroup of t consists only of 1 and t, so the
point-displacement kernel condition implies the full commutator containment.

This is the sufficient half-order version of the coatom construction in
Stellmacher (9.10), printed p.57. It includes the trivial displacement case
without making an arbitrary coatom choice and is independent of the graph
or the later (9.4) application.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

private theorem cyclic_two_cases {G : Type*} [Group G] (actor : G) (hactor : actor ^ 2 = 1)
    (element : G) (helement : element ∈ zpowers actor) : element = 1 ∨ element = actor := by
  let K : Subgroup G :=
    { carrier := {element | element = 1 ∨ element = actor}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro left right (rfl | rfl) (rfl | rfl) <;> simp_all [pow_two]
      inv_mem' := by
        rintro element (rfl | rfl)
        · simp
        · right
          exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hactor) }
  exact (zpowers_le.mpr (show actor ∈ K from Or.inr rfl)) helement

public theorem exists_large_subgroup_commutator_le_of_central_bound
    {G : Type*} [Group G] [Finite G]
    (K U R Z : Subgroup G) [IsMulCommutative U]
    (hKU : K ≤ normalizer (U : Set G)) (hRU : R ≤ U) (hZU : Z ≤ U)
    (hZcard : Nat.card Z = 2)
    (hcentral : K ≤ centralizer ((R ⊔ Z : Subgroup G) : Set G))
    (actor : G) (hactorU : actor ∈ U) (hactorPow : actor ^ 2 = 1)
    (hcomm : ⁅K, zpowers actor⁆ ≤ R ⊔ Z) :
    ∃ A : Subgroup G, A ≤ K ∧ Nat.card K ≤ 2 * Nat.card A ∧ ⁅A, zpowers actor⁆ ≤ R := by
  let _ : Normalizes K U := ⟨hKU⟩
  let M : Subgroup U := R.subgroupOf U ⊔ Z.subgroupOf U
  have hM : (R ⊔ Z).subgroupOf U = M := subgroupOf_sup hRU hZU
  have hMmap : M.map U.subtype = R ⊔ Z := by
    change (R.subgroupOf U ⊔ Z.subgroupOf U).map U.subtype = _
    rw [map_sup, map_subgroupOf_eq_of_le hRU, map_subgroupOf_eq_of_le hZU]
  have hquotient : Nat.card (M ⧸ (R.subgroupOf U).subgroupOf M) ≤ 2 := by
    rw [← index_eq_card]
    change (R.subgroupOf U).relIndex (R.subgroupOf U ⊔ Z.subgroupOf U) ≤ 2
    rw [relIndex_sup_left]
    have hdiv := relIndex_dvd_card (R.subgroupOf U) (Z.subgroupOf U)
    have hZnative : Nat.card (Z.subgroupOf U) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv).trans hZcard
    rw [hZnative] at hdiv
    exact Nat.le_of_dvd (by decide) hdiv
  let point : U := ⟨actor, hactorU⟩
  have hfixed : ∀ mover : K, ∀ value : U, value ∈ M → mover • value = value := by
    intro mover value hvalue
    have hvalueAmbient : (value : G) ∈ R ⊔ Z := by
      rw [← hMmap]
      exact mem_map_of_mem U.subtype hvalue
    have hcommute := mem_centralizer_iff.mp (hcentral mover.property) value hvalueAmbient
    apply Subtype.ext
    change (mover : G) * (value : G) * (mover : G)⁻¹ = (value : G)
    change (value : G) * (mover : G) = (mover : G) * (value : G) at hcommute
    rw [← hcommute, mul_inv_cancel_right]
  have hdisplacement : ∀ mover : K, point⁻¹ * (mover • point) ∈ M := by
    intro mover
    rw [← hM]
    change actor⁻¹ * ((mover : G) * actor * (mover : G)⁻¹) ∈ R ⊔ Z
    have h := hcomm
    rw [commutator_comm] at h
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      h (commutator_mem_commutator ((zpowers actor).inv_mem (mem_zpowers actor)) mover.property)
  obtain ⟨native, _, hcard, hnative⟩ :=
    exists_large_subgroup_of_fixed_displacement_quotient M (R.subgroupOf U)
      hfixed point hdisplacement hquotient
  refine ⟨native.map K.subtype, map_subtype_le native, ?_, ?_⟩
  · rwa [card_map_of_injective K.subtype_injective]
  · apply commutator_le.mpr
    rintro mover ⟨nativeMover, hnativeMover, rfl⟩ other hother
    rcases cyclic_two_cases actor hactorPow other hother with hotherOne | hotherActor
    · subst other
      simp
    · subst other
      have h := (R.subgroupOf U).inv_mem (hnative nativeMover hnativeMover)
      change (actor⁻¹ * ((nativeMover : G) * actor * (nativeMover : G)⁻¹))⁻¹ ∈ R at h
      have hactorInv : actor⁻¹ = actor :=
        inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hactorPow)
      change ⁅(nativeMover : G), actor⁆ ∈ R
      simpa only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc, hactorInv] using h

end Subgroup
