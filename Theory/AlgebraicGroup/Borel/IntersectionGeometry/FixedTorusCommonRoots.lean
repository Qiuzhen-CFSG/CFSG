module

public import Theory.AlgebraicGroup.Borel.RootBorelDecomposition
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedCharacterSupport

/-!
The common-root argument for two compatible Borel witnesses at a fixed torus.

The torus factorization is unconditional: if `x = t * u` lies in both Borels,
then `u` lies in the intersection of the first radical with the second Borel.
That intersection is a closed unipotent subgroup, so it lies in the second
radical. This avoids assuming that the Borel intersection is connected.

For the root identification, character support detects contained root groups
once the positive character monoid contains no other roots. Generation of the
torus-invariant radical intersection then gives precisely the common roots.
These last two geometric inputs remain explicit in the assembly below; this
module does not yet prove the unconditional common-root formula.

Sources: GLS3, Theorem 1.11.4 (`refs/KGroup/GLS3/Chapter1.tex`), and Borel,
*Linear Algebraic Groups*, §§14.4–14.5 (`refs/KGroup/Bor1/Chapter4.tex`).
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {T B C : ClosedSubgroup G} {D : RootGroupData G T}
variable {P Q : Set D.Root}

omit [IsAlgClosed k] in
private theorem witness_torus_le (hB : IsBorelOfPositiveSystem D P B) : T ≤ B := by
  change T.toSubgroup ≤ B.toSubgroup
  rw [hB.torus_unipotent_generate]
  exact le_sup_left

omit [IsAlgClosed k] in
private theorem witness_root_le (hB : IsBorelOfPositiveSystem D P B)
    {a : D.Root} (ha : a ∈ P) : D.rootSubgroup a ≤ hB.unipotent := by
  change (D.rootSubgroup a).toSubgroup ≤ hB.unipotent.toSubgroup
  rw [hB.root_generated]
  exact rootSubgroup_le_RootSubgroupGenerated D ha

private theorem unipotent_of_containment {V U : ClosedSubgroup G}
    (hVU : V ≤ U) (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    IsUnipotentAlgebraicGroup V.carrierVariety := by
  intro v
  have hxV : V.includePoint v ∈ V := (V.pointEquiv v).property
  have hxU : V.includePoint v ∈ U := hVU hxV
  have hx : IsUnipotentElement G (V.includePoint v) :=
    (closedSubgroup_unipotentElement_iff U hxU).mpr
      (hU (U.pointEquiv.symm ⟨V.includePoint v, hxU⟩))
  have hv := (closedSubgroup_unipotentElement_iff V hxV).mp hx
  have heq : V.pointEquiv.symm ⟨V.includePoint v, hxV⟩ = v := by
    apply V.pointEquiv.injective
    apply Subtype.ext
    exact congrArg Subtype.val (V.pointEquiv.apply_symm_apply _)
  rwa [heq] at hv

/-- Two compatible Borel witnesses have a common-torus factorization using
the intersection of their actual unipotent radicals. No connectedness of
either intersection is assumed. -/
public theorem fixedTorus_inter_pointwise_radicals
    (hBP : IsBorelOfPositiveSystem D P B)
    (hCQ : IsBorelOfPositiveSystem D Q C) (x : Variety.Point G) :
    x ∈ B.inter C ↔ ∃ t v, t ∈ T ∧
      v ∈ hBP.unipotent.inter hCQ.unipotent ∧ x = t * v := by
  have hUC : hBP.unipotent.inter C ≤ hCQ.unipotent := by
    apply hCQ.radical.contains_unipotent_closedSubgroup
      hCQ.borel.connected hCQ.borel.solvable
    · exact fun _ hx => hx.2
    · exact unipotent_of_containment (fun _ hx => hx.1) hBP.radical.2.1
  constructor
  · intro hx
    obtain ⟨t, v, ht, hv, htv⟩ :=
      (BorelOfPositiveSystem.pointwise_decomposition hBP x).mp hx.1
    have hvU : v ∈ hBP.unipotent := by
      change v ∈ hBP.unipotent.toSubgroup
      rwa [hBP.root_generated]
    have hvC : v ∈ C := by
      change v ∈ C.toSubgroup
      have h := C.toSubgroup.mul_mem
        (C.toSubgroup.inv_mem (witness_torus_le hCQ ht)) hx.2
      simpa only [htv, inv_mul_cancel_left] using h
    exact ⟨t, v, ht, ⟨hvU, hUC ⟨hvU, hvC⟩⟩, htv⟩
  · rintro ⟨t, v, ht, hv, rfl⟩
    exact ⟨B.toSubgroup.mul_mem (witness_torus_le hBP ht) (hBP.radical.1 hv.1),
      C.toSubgroup.mul_mem (witness_torus_le hCQ ht) (hCQ.radical.1 hv.2)⟩

/-- Subgroup form of the common-torus factorization. -/
public theorem fixedTorus_inter_eq_torus_sup_radicals
    (hBP : IsBorelOfPositiveSystem D P B)
    (hCQ : IsBorelOfPositiveSystem D Q C) :
    (B.inter C).toSubgroup = T.toSubgroup ⊔
      (hBP.unipotent.inter hCQ.unipotent).toSubgroup := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, v, ht, hv, rfl⟩ :=
      (fixedTorus_inter_pointwise_radicals hBP hCQ x).mp hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hv)
  · apply sup_le
    · exact fun _ ht => ⟨witness_torus_le hBP ht, witness_torus_le hCQ ht⟩
    · exact fun _ hv => ⟨hBP.radical.1 hv.1, hCQ.radical.1 hv.2⟩

omit [IsAlgClosed k] in
/-- The radical intersection is invariant under the shared torus, with the
inverse-conjugation convention used by `IsClosedSubgroupInvariant`. -/
public theorem fixedTorus_radical_inter_invariant
    (hBP : IsBorelOfPositiveSystem D P B)
    (hCQ : IsBorelOfPositiveSystem D Q C) :
    IsClosedSubgroupInvariant T (hBP.unipotent.inter hCQ.unipotent) := by
  intro t ht v hv
  have htinv : t⁻¹ ∈ T := T.toSubgroup.inv_mem ht
  have hB := hBP.radical.2.2.1 t⁻¹ (witness_torus_le hBP htinv) v hv.1
  have hC := hCQ.radical.2.2.1 t⁻¹ (witness_torus_le hCQ htinv) v hv.2
  change t⁻¹ * v * t ∈ hBP.unipotent ∧ t⁻¹ * v * t ∈ hCQ.unipotent
  simpa only [inv_inv] using And.intro hB hC

/-- Character support gives exact root containment for an actual Borel
witness, provided its positive character monoid contains only positive roots. -/
public theorem fixedTorus_root_le_borel_iff_of_character_support
    (hT : IsSubtorus T) (hD : D.IsRealization)
    (hBP : IsBorelOfPositiveSystem D P B)
    (hPcone : ∀ a, D.rootWeight a ∈ Submonoid.closure (D.rootWeight '' P) → a ∈ P)
    (a : D.Root) : D.rootSubgroup a ≤ B ↔ a ∈ P := by
  constructor
  · intro ha
    apply hPcone a
    apply rootWeight_mem_submonoidClosure_of_rootSubgroup_le_generated_sup_torus
      hT D hD P a
    have hB : B.toSubgroup = RootSubgroupGenerated D P ⊔ T.toSubgroup := by
      rw [hBP.torus_unipotent_generate, hBP.root_generated, sup_comm]
    rw [← hB]
    exact ha
  · intro ha
    exact fun _ hx => hBP.radical.1 (witness_root_le hBP ha hx)

/-- The radical version of root detection follows from the same character
support argument, since positive root groups generate the supplied radical. -/
public theorem fixedTorus_root_le_radical_iff_of_character_support
    (hT : IsSubtorus T) (hD : D.IsRealization)
    (hBP : IsBorelOfPositiveSystem D P B)
    (hPcone : ∀ a, D.rootWeight a ∈ Submonoid.closure (D.rootWeight '' P) → a ∈ P)
    (a : D.Root) : D.rootSubgroup a ≤ hBP.unipotent ↔ a ∈ P := by
  constructor
  · intro ha
    exact (fixedTorus_root_le_borel_iff_of_character_support hT hD hBP hPcone a).mp
      (fun _ hx => hBP.radical.1 (ha hx))
  · exact witness_root_le hBP

/-- Generation by contained roots identifies the radical intersection with
the common positive-root subgroup. The generation and positive-cone inputs
are independent geometric prerequisites, not fields of a Borel witness. -/
public theorem fixedTorus_radical_inter_eq_commonRoots_of_generation
    (hT : IsSubtorus T) (hD : D.IsRealization)
    (hBP : IsBorelOfPositiveSystem D P B)
    (hCQ : IsBorelOfPositiveSystem D Q C)
    (hPcone : ∀ a, D.rootWeight a ∈ Submonoid.closure (D.rootWeight '' P) → a ∈ P)
    (hQcone : ∀ a, D.rootWeight a ∈ Submonoid.closure (D.rootWeight '' Q) → a ∈ Q)
    (hgen : ∀ X : ClosedSubgroup G, X ≤ hBP.unipotent →
      IsClosedSubgroupInvariant T X →
      X.toSubgroup = RootSubgroupGenerated D {a | D.rootSubgroup a ≤ X}) :
    (hBP.unipotent.inter hCQ.unipotent).toSubgroup =
      RootSubgroupGenerated D (P ∩ Q) := by
  have hroots : {a | D.rootSubgroup a ≤ hBP.unipotent.inter hCQ.unipotent} =
      P ∩ Q := by
    ext a
    change (D.rootSubgroup a ≤ hBP.unipotent.inter hCQ.unipotent) ↔ a ∈ P ∩ Q
    constructor
    · intro ha
      exact ⟨(fixedTorus_root_le_radical_iff_of_character_support
        hT hD hBP hPcone a).mp (fun x hx => (ha hx).1),
        (fixedTorus_root_le_radical_iff_of_character_support
          hT hD hCQ hQcone a).mp (fun x hx => (ha hx).2)⟩
    · intro ha x hx
      exact ⟨witness_root_le hBP ha.1 hx, witness_root_le hCQ ha.2 hx⟩
  rw [hgen (hBP.unipotent.inter hCQ.unipotent) (fun _ hx => hx.1)
    (fixedTorus_radical_inter_invariant hBP hCQ), hroots]

/-- Conditional assembly of the common-root formula. To obtain the source
statement, the positive-cone and invariant-generation premises must still be
proved from reductivity, maximality of the torus, and the realized root data. -/
public theorem fixedTorus_inter_eq_commonRoots_of_generation
    (hT : IsSubtorus T) (hD : D.IsRealization)
    (hBP : IsBorelOfPositiveSystem D P B)
    (hCQ : IsBorelOfPositiveSystem D Q C)
    (hPcone : ∀ a, D.rootWeight a ∈ Submonoid.closure (D.rootWeight '' P) → a ∈ P)
    (hQcone : ∀ a, D.rootWeight a ∈ Submonoid.closure (D.rootWeight '' Q) → a ∈ Q)
    (hgen : ∀ X : ClosedSubgroup G, X ≤ hBP.unipotent →
      IsClosedSubgroupInvariant T X →
      X.toSubgroup = RootSubgroupGenerated D {a | D.rootSubgroup a ≤ X}) :
    (B.inter C).toSubgroup = T.toSubgroup ⊔ RootSubgroupGenerated D (P ∩ Q) := by
  rw [fixedTorus_inter_eq_torus_sup_radicals hBP hCQ,
    fixedTorus_radical_inter_eq_commonRoots_of_generation hT hD hBP hCQ hPcone hQcone hgen]

end Theory.AlgebraicGroup.BorelIntersectionGeometry
