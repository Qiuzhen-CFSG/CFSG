module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.Reduction
public import Theory.Mathieu.M24.LocalGeometry.Stabilizers
public import Theory.GroupTheory.ComponentLocalIntersection
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The M24 geometric pair through the actual component cover

Restrict the supplied Sylow subgroup to the subnormal component, and map it
through the given quotient L/O₂(L) ≃ M24. The native octad/sextet pair over
this model Sylow generates M24 and has self-centralizing intrinsic two-cores.
The full preimages retain the entire two-group kernel, so the core conditions
lift without assuming that the central cover splits.

Only N_S(L) acts on L. Its quotient action preserves the model Sylow, hence
both chosen stabilizers. The component-orbit theorem therefore gives
characteristic two after adjoining all of S. The source involution makes each
core nontrivial. Relative self-normalization gives the exact intersections
with L, even when S permutes components. This constructs every field of the
published GeometryPair; the independent block obstruction is still needed
for the M24 exclusion itself.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3, Table 5.3e.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
open M24LocalGeometry
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Restrict the supplied Sylow subgroup along component subnormality inside H. -/
noncomputable def componentSylow (h : LocalSetup H L M S z) : Sylow 2 L :=
  h.exists_component_sylow.choose

/-- The component Sylow subgroup is the literal intersection with the supplied S. -/
theorem componentSylow_map (h : LocalSetup H L M S z) :
    (componentSylow h : Subgroup L).map L.subtype =
      L ⊓ (S : Subgroup H).map H.subtype := h.exists_component_sylow.choose_spec

/-- Membership in the component Sylow is membership in the ambient Sylow image. -/
theorem mem_componentSylow (h : LocalSetup H L M S z) (x : L) :
    x ∈ (componentSylow h : Subgroup L) ↔
      (x : G) ∈ (S : Subgroup H).map H.subtype := by
  rw [← mem_map_iff_mem L.subtype_injective, componentSylow_map h]
  exact and_iff_right x.property

/-- The model Sylow subgroup obtained through the specified quotient map. -/
noncomputable def modelSylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) : Sylow 2 M24 := by
  let := h.finite
  exact (componentSylow h).mapSurjective (quotientMap_surjective d)

/-- The underlying model Sylow is the image of the actual component Sylow. -/
theorem modelSylow_coe (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) :
    (modelSylow h d : Subgroup M24) = (componentSylow h).map (quotientMap d) := rfl

/-- The genuine action on the characteristic two-core quotient, transported by d. -/
noncomputable def modelAut (d : SporadicQuotientInput L z .m24) :
    MulAut L →* MulAut M24 :=
  (MulAut.congr d.quotientIso).toMonoidHom.comp (quotientAut (pCore 2 L))

/-- The quotient action commutes with the supplied model map. -/
theorem modelAut_apply (d : SporadicQuotientInput L z .m24) (a : MulAut L) (x : L) :
    modelAut d a (quotientMap d x) = quotientMap d (a x) := by
  change d.quotientIso (quotientAut (pCore 2 L) a
    (d.quotientIso.symm (d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)))) = _
  rw [d.quotientIso.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- Only the component stabilizer inside the acting subgroup acts on the model. -/
noncomputable def normalizerModelAction (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) : (A ⊓ normalizer (L : Set G) : Subgroup G) →* MulAut M24 :=
  (modelAut d).comp (L.normalizerMonoidHom.comp (inclusion inf_le_right))

/-- The model action is induced by literal ambient conjugation. -/
theorem normalizerModelAction_apply (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) (a : (A ⊓ normalizer (L : Set G) : Subgroup G)) (x : L) :
    normalizerModelAction d A a (quotientMap d x) =
      quotientMap d ⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp a.property.2 x).mp x.property⟩ :=
  modelAut_apply d _ x

/-- The component stabilizer preserves the restricted Sylow and its quotient image. -/
theorem normalizerModelAction_preserves_sylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24)
    (a : ((S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) : Subgroup G)) :
    (modelSylow h d : Subgroup M24).map
      (normalizerModelAction d ((S : Subgroup H).map H.subtype) a).toMonoidHom =
        (modelSylow h d : Subgroup M24) := by
  have hstable (a : ((S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) : Subgroup G))
      (r : M24) (hr : r ∈ (modelSylow h d : Subgroup M24)) :
      normalizerModelAction d ((S : Subgroup H).map H.subtype) a r ∈
        (modelSylow h d : Subgroup M24) := by
    obtain ⟨x, hx, rfl⟩ := hr
    rw [normalizerModelAction_apply]
    apply mem_map_of_mem
    apply (mem_componentSylow h _).mpr
    exact ((S : Subgroup H).map H.subtype).mul_mem
      (((S : Subgroup H).map H.subtype).mul_mem a.property.1
        ((mem_componentSylow h x).mp hx))
      (((S : Subgroup H).map H.subtype).inv_mem a.property.1)
  apply le_antisymm
  · rintro r ⟨x, hx, rfl⟩
    exact hstable a x hx
  · intro r hr
    refine ⟨normalizerModelAction d ((S : Subgroup H).map H.subtype) a⁻¹ r,
      hstable a⁻¹ r hr, ?_⟩
    rw [map_inv]
    exact MulEquiv.apply_symm_apply _ _

/-- Every model Sylow overgroup has a preimage invariant under N_S(L). -/
theorem lift_normalized (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (P : Subgroup M24)
    (hP : (modelSylow h d : Subgroup M24) ≤ P) :
    (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (lift d P : Set G) := by
  let A := (S : Subgroup H).map H.subtype
  have hstable (a : (A ⊓ normalizer (L : Set G) : Subgroup G))
      (x : G) (hx : x ∈ lift d P) : (a : G) * x * (a : G)⁻¹ ∈ lift d P := by
    obtain ⟨x, hx, rfl⟩ := hx
    refine ⟨⟨(a : G) * x * (a : G)⁻¹,
      (mem_normalizer_iff.mp a.property.2 x).mp x.property⟩, ?_, rfl⟩
    have hm : normalizerModelAction d A a (quotientMap d x) ∈ P := by
      rw [← Stabilizers.automorphism_preserves_overgroup (modelSylow h d) P hP
        (normalizerModelAction d A a) (normalizerModelAction_preserves_sylow h d a)]
      exact mem_map_of_mem _ hx
    rw [normalizerModelAction_apply] at hm
    exact hm
  intro a ha
  apply mem_normalizer_iff.mpr
  intro x
  refine ⟨hstable ⟨a, ha⟩ x, ?_⟩
  intro hx
  have hi := hstable (⟨a, ha⟩ : (A ⊓ normalizer (L : Set G) : Subgroup G))⁻¹ _ hx
  simpa only [coe_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
    mul_assoc, inv_mul_cancel, mul_one] using hi

/-- Normalizer transport retains the full preimage and is relative to L. -/
theorem lift_normalizer (d : SporadicQuotientInput L z .m24) (P : Subgroup M24) :
    lift d (normalizer (P : Set M24)) = L ⊓ normalizer (lift d P : Set G) := by
  have hs : (lift d P).subgroupOf L = P.comap (quotientMap d) :=
    comap_map_eq_self_of_injective L.subtype_injective _
  change ((normalizer (P : Set M24)).comap (quotientMap d)).map L.subtype = _
  rw [comap_normalizer_eq_of_surjective P (quotientMap_surjective d), ← hs,
    ← subgroupOf_normalizer_eq (lift_le d P), subgroupOf_map_subtype, inf_comm]

/-- Adjoining S does not enlarge the induced subgroup on the distinguished component. -/
theorem localOvergroup_intersection (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (P : Subgroup M24)
    (hP : (modelSylow h d : Subgroup M24) ≤ P) :
    L ⊓ localOvergroup d ((S : Subgroup H).map H.subtype) P = lift d P := by
  apply h.component.relative_local_adjoin_intersection h.component_le (lift_le d P)
    (map_subtype_le _) (lift_normalized h d P hP)
  rw [← lift_normalizer]
  exact map_mono (comap_mono (Stabilizers.sylow_overgroup_selfNormalizing (modelSylow h d) P hP))

/-- The intrinsic core condition lifts through the entire O₂(L) kernel. -/
theorem pullback_core_selfCentralizing (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (P : Subgroup M24)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 (P.comap (quotientMap d)) : Set (P.comap (quotientMap d))) ≤
      pCore 2 (P.comap (quotientMap d)) := by
  let := h.finite
  have : (quotientMap d).range.Normal := by
    rw [MonoidHom.range_eq_top.mpr (quotientMap_surjective d)]
    infer_instance
  apply (quotientMap d).centralizer_pCore_comap_of_normal_range _ P hP
  rw [quotientMap_ker]
  exact pCore_isPGroup

/-- A model Sylow overgroup with characteristic two gives all three HeOver clauses. -/
theorem localOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (P : Subgroup M24)
    (hP : (modelSylow h d : Subgroup M24) ≤ P)
    (hself : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    localOvergroup d ((S : Subgroup H).map H.subtype) P ∈
      Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  let := h.finite
  have hs : lift d P ⊓ centralizer ((lift d P).pCoreIn 2 : Set G) ≤
      (lift d P).pCoreIn 2 := by
    rw [lift, ← map_pCoreIn_of_injective 2 (P.comap (quotientMap d)) L.subtype
      L.subtype_injective]
    exact (inf_centralizer_map_le_iff _ _ L.subtype L.subtype_injective).mpr
      ((inf_centralizer_pCoreIn_le_iff 2 _).mpr (pullback_core_selfCentralizing h d P hself))
  have he := h.component.relative_local_adjoin_centralizer h.component_le
    (lift_le d P) (map_subtype_le (S : Subgroup H))
    (S.isPGroup'.map H.subtype) (lift_normalized h d P hP) hs
  refine ⟨he, ?_, le_localOvergroup d _ P⟩
  intro hbot
  change (lift d P ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2 = ⊥ at hbot
  rw [hbot] at he
  have hz := he ⟨le_localOvergroup d _ P h.mem_sylow, by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]⟩
  have hz1 : z = 1 := hz
  simpa [hz1] using h.involution

/-- Construct the actual geometric pair required by the M24 component-exclusion reduction. -/
theorem geometryPair_nonempty (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) :
    Nonempty (GeometryPair d ((S : Subgroup H).map H.subtype)) := by
  obtain ⟨P, Q, hPg, hQg, hPT, hQT, hPc, hQc, hgen⟩ :=
    Stabilizers.exists_pair_over_sylow (modelSylow h d)
  exact ⟨{
    left := P
    right := Q
    left_geometry := hPg
    right_geometry := hQg
    generated := hgen
    left_intersection := localOvergroup_intersection h d P hPT
    right_intersection := localOvergroup_intersection h d Q hQT
    left_even := localOvergroup_mem_HeOver h d P hPT hPc
    right_even := localOvergroup_mem_HeOver h d Q hQT hQc
  }⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

end
