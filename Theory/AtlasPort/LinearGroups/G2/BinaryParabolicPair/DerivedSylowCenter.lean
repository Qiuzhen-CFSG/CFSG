module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Central involutions in the actual binary derived Sylow subgroup

The long-root quotient identifies the intersection of the six positive root
groups with G₂(2)′ by the equation `t₂ + t₃ + t₅ = 0`. The root multiplication
law shows that a central element in this intersection whose square is one
has only its first coordinate nonzero. Thus its only nonidentity central
involution is the distinguished long-root element.

Restriction of the existing ambient Sylow subgroup to the normal commutator
subgroup supplies an actual Sylow witness with exactly this ambient image.
No comparison with an abstract Sylow model is needed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.1.12(8), printed p.263, and the model inspection in
15.4.15, printed p.1161. The root coordinates and their multiplication are those
of the licensed ATLAS port imported through `Restriction`.
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem unipotentProduct_mem_derived_iff (t : Fin 6 → ZMod 2) :
    unipotentProduct t ∈ DerivedModel ↔ t 2 + t 3 + t 5 = 0 := by
  change unipotentProduct t ∈ commutator (Model (ZMod 2)) ↔ _
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (unipotentProduct t) = 1 ↔ _
  simp only [unipotentProduct, map_mul, BinaryException.project_A,
    BinaryException.project_B, BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  rw [← map_mul, ← map_mul, rootF_add, rootF_add]
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hb (t 2 + t 3 + t 5) with h | h
  · simp [h, rootF_zero]
  · rw [h]
    exact iff_of_false quotientBit_ne_one (by decide)

private theorem central_involution_parameters : ∀ t : Fin 6 → ZMod 2,
    t 2 + t 3 + t 5 = 0 →
    unipotentProductParameters t t = 0 →
    (∀ u : Fin 6 → ZMod 2, u 2 + u 3 + u 5 = 0 →
      unipotentProductParameters u t = unipotentProductParameters t u) →
    t = ![t 0, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Every central element of the actual derived overlap whose square is one
lies in the distinguished order-two subgroup. -/
theorem derivedSylowAmbient_central_involution_mem {g : Model (ZMod 2)}
    (hg : g ∈ derivedSylowAmbient) (hsq : g ^ 2 = 1)
    (hcent : ∀ u ∈ derivedSylowAmbient, u * g = g * u) : g ∈ distinguished := by
  obtain ⟨hgU, hgD⟩ := hg
  rw [unipotent_eq_range] at hgU
  obtain ⟨t, rfl⟩ := hgU
  have ht := (unipotentProduct_mem_derived_iff t).mp hgD
  have ht2 : unipotentProductParameters t t = 0 := by
    apply unipotentProduct_injective
    rw [← unipotentProduct_mul, ← pow_two, hsq, unipotentProduct_zero]
  have htc : ∀ u : Fin 6 → ZMod 2, u 2 + u 3 + u 5 = 0 →
      unipotentProductParameters u t = unipotentProductParameters t u := by
    intro u hu
    apply unipotentProduct_injective
    rw [← unipotentProduct_mul, ← unipotentProduct_mul]
    exact hcent _ ⟨unipotentProduct_mem _, (unipotentProduct_mem_derived_iff u).mpr hu⟩
  rw [central_involution_parameters t ht ht2 htc]
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hb (t 0) with h | h
  · simp [h, unipotentProduct]
  · simpa [h, unipotentProduct] using
      (show rootA (1 : ZMod 2) ∈ distinguished from Subgroup.mem_zpowers z)

/-- Restrict the positive-root Sylow subgroup to the actual commutator group. -/
noncomputable def derivedSylow : Sylow 2 DerivedModel :=
  (commonSylow.exists_sylow_map_eq_inf_of_normal DerivedModel).choose

/-- The chosen derived Sylow subgroup has the original intersection embedding. -/
theorem derivedSylow_map_subtype :
    (derivedSylow : Subgroup DerivedModel).map DerivedModel.subtype =
      derivedSylowAmbient :=
  (commonSylow.exists_sylow_map_eq_inf_of_normal DerivedModel).choose_spec

end Atlas.G2.BinaryParabolicPair
