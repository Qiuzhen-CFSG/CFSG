module

public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.FixedSpaceCodimension
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Mathlib.Algebra.DirectSum.Module
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Component sections in a common central quotient

When each factor centralizes the other factors' moved sections, the local
fixed-space kernel is exactly the global fixed-space kernel on that section.
Consequently the literal central quotients embed independently into the common
quotient. Their direct sum is the central quotient of the whole moved space.
Conjugation by the original ambient action carries these summands along with
the actual factors; neither independence nor an ambient splitting is assumed.

The binary formulation serves the module decomposition in Aschbacher–Smith,
B.6.9(2), printed pp.115–117 (1 March 2004 manuscript).
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V ι : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem fixedSpace_iSup_family (L : ι → Subgroup G) :
    fixedSpace ρ (⨆ i, L i) = ⨅ i, fixedSpace ρ (L i) :=
  ρ.invariants_comp_iSup L

theorem subspaceCommutator_iSup_family (L : ι → Subgroup G) :
    subspaceCommutator ρ ⊤ (⨆ i, L i) = ⨆ i, subspaceCommutator ρ ⊤ (L i) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    have hh : ∀ v : V, ρ g v - v ∈ ⨆ i, subspaceCommutator ρ ⊤ (L i) := by
      refine Subgroup.iSup_induction L
        (C := fun g => ∀ v : V, ρ g v - v ∈ ⨆ i, subspaceCommutator ρ ⊤ (L i))
        hg ?_ ?_ ?_
      · intro i g hg v
        exact le_iSup (fun i => subspaceCommutator ρ ⊤ (L i)) i
          (Submodule.subset_span ⟨g,hg,v,Submodule.mem_top,rfl⟩)
      · intro v
        simp
      · intro a b ha hb v
        have hh := (⨆ i, subspaceCommutator ρ ⊤ (L i)).add_mem (ha (ρ b v)) (hb v)
        simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hh
    exact hh v
  · refine iSup_le fun i => Submodule.span_le.mpr ?_
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact Submodule.subset_span ⟨g,le_iSup L i hg,v,hv,rfl⟩

variable (L : ι → Subgroup G) (W : ι → Submodule (ZMod 2) V)
  (hcross : ∀ i j, i ≠ j → W i ≤ fixedSpace ρ (L j))

include hcross in
theorem family_fixed_kernel (i : ι) :
    (fixedSpace ρ (⨆ j, L j)).comap (W i).subtype =
      (fixedSpace ρ (L i)).comap (W i).subtype := by
  classical
  apply le_antisymm
  · intro w hw l
    exact hw ⟨l, le_iSup L i l.property⟩
  · intro w hw
    rw [Submodule.mem_comap, fixedSpace_iSup_family, Submodule.mem_iInf]
    intro j
    by_cases h : i = j
    · subst j
      exact hw
    · exact hcross i j h w.property

@[expose] noncomputable def familyCentralQuotientMap (i : ι) :
    centralQuotient ρ (L i) (W i) →ₗ[ZMod 2] (V ⧸ fixedSpace ρ (⨆ j, L j)) :=
  ((fixedSpace ρ (L i)).comap (W i).subtype).liftQ
    ((fixedSpace ρ (⨆ j, L j)).mkQ.comp (W i).subtype) (by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, family_fixed_kernel ρ L W hcross i])

@[simp] theorem familyCentralQuotientMap_mk (i : ι) (w : W i) :
    familyCentralQuotientMap ρ L W hcross i (Submodule.Quotient.mk w) =
      (fixedSpace ρ (⨆ j, L j)).mkQ w := rfl

theorem familyCentralQuotientMap_injective (i : ι) :
    Function.Injective (familyCentralQuotientMap ρ L W hcross i) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, family_fixed_kernel ρ L W hcross i]

theorem familyCentralQuotientMap_range (i : ι) :
    (familyCentralQuotientMap ρ L W hcross i).range =
      (W i).map (fixedSpace ρ (⨆ j, L j)).mkQ := by
  rw [familyCentralQuotientMap, Submodule.range_liftQ, LinearMap.range_comp,
    Submodule.range_subtype]

include hcross in
theorem familyCentralQuotient_independent :
    iSupIndep (fun i => (W i).map (fixedSpace ρ (⨆ j, L j)).mkQ) := by
  intro i
  apply disjoint_iff_inf_le.mpr
  intro v hv
  obtain ⟨w,hw,rfl⟩ := hv.1
  have hC : fixedSpace ρ (⨆ j, L j) ≤ fixedSpace ρ (L i) :=
    ρ.invariants_comp_subtype_antitone (le_iSup L i)
  have hs : (⨆ j, ⨆ (_ : j ≠ i), (W j).map (fixedSpace ρ (⨆ k, L k)).mkQ) ≤
      (fixedSpace ρ (L i)).map (fixedSpace ρ (⨆ k, L k)).mkQ :=
    iSup_le fun j => iSup_le fun hj => Submodule.map_mono (hcross j i hj)
  have hh : w ∈ fixedSpace ρ (⨆ j, L j) ⊔ fixedSpace ρ (L i) := by
    rw [← Submodule.comap_map_mkQ]
    exact hs hv.2
  have hwf : (⟨w,hw⟩ : W i) ∈ (fixedSpace ρ (L i)).comap (W i).subtype :=
    (sup_le hC le_rfl) hh
  rw [← family_fixed_kernel ρ L W hcross i] at hwf
  exact (Submodule.Quotient.mk_eq_zero _).mpr hwf


noncomputable def familyCentralQuotientEquiv (i : ι) :
    centralQuotient ρ (L i) (W i) ≃ₗ[ZMod 2]
      (W i).map (fixedSpace ρ (⨆ j, L j)).mkQ :=
  (LinearEquiv.ofInjective _ (familyCentralQuotientMap_injective ρ L W hcross i)).trans
    (LinearEquiv.ofEq _ _ (familyCentralQuotientMap_range ρ L W hcross i))

theorem familyCentralQuotientMap_equivariant [(⨆ j, L j).Normal]
    (i : ι) (hW : L i ≤ subspaceStabilizer ρ (W i))
    (g : L i) (w : centralQuotient ρ (L i) (W i)) :
    familyCentralQuotientMap ρ L W hcross i
        (centralQuotientRepresentation ρ (L i) (W i) hW g w) =
      fixedQuotient ρ (⨆ j, L j) g
        (familyCentralQuotientMap ρ L W hcross i w) := by
  induction w using Submodule.Quotient.induction_on with | _ w => rfl

theorem familyCentralQuotient_iSup_range
    (hmoved : ∀ i, W i = subspaceCommutator ρ ⊤ (L i)) :
    (⨆ i, (familyCentralQuotientMap ρ L W hcross i).range) =
      (subspaceCommutator ρ ⊤ (⨆ i, L i)).map (fixedSpace ρ (⨆ j, L j)).mkQ := by
  simp_rw [familyCentralQuotientMap_range, hmoved]
  rw [subspaceCommutator_iSup_family, Submodule.map_iSup]

open scoped DirectSum
noncomputable def familyCentralDirectSumEquiv [DecidableEq ι]
    (hmoved : ∀ i, W i = subspaceCommutator ρ ⊤ (L i)) :
    (⨁ i, (W i).map (fixedSpace ρ (⨆ j, L j)).mkQ) ≃ₗ[ZMod 2]
      (subspaceCommutator ρ ⊤ (⨆ i, L i)).map (fixedSpace ρ (⨆ j, L j)).mkQ :=
  (LinearEquiv.ofInjective _
    (familyCentralQuotient_independent ρ L W hcross).dfinsupp_lsum_injective).trans
      (LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap.trans (by
        simp_rw [hmoved]
        rw [subspaceCommutator_iSup_family, Submodule.map_iSup])))

private noncomputable def movedQuotientImageEquiv (K : Subgroup G)
    (I : Submodule (ZMod 2) V) :
    centralQuotient ρ K I ≃ₗ[ZMod 2] I.map (fixedSpace ρ K).mkQ := by
  have e := familyCentralQuotientEquiv ρ (fun _ : Unit => K) (fun _ : Unit => I)
    (by intro i j h; exact (h (Subsingleton.elim _ _)).elim) ()
  change centralQuotient ρ K I ≃ₗ[ZMod 2] I.map (fixedSpace ρ (⨆ _ : Unit, K)).mkQ at e
  rw [iSup_const] at e
  exact e

/-- The literal component central quotients sum to the central quotient of the moved space. -/
noncomputable def familyMovedCentralQuotientEquiv [DecidableEq ι]
    (hmoved : ∀ i, W i = subspaceCommutator ρ ⊤ (L i)) :
    (⨁ i, centralQuotient ρ (L i) (W i)) ≃ₗ[ZMod 2]
      centralQuotient ρ (⨆ i, L i) (subspaceCommutator ρ ⊤ (⨆ i, L i)) :=
  (DirectSum.congrLinearEquiv (familyCentralQuotientEquiv ρ L W hcross)).trans
    ((familyCentralDirectSumEquiv ρ L W hcross hmoved).trans
      (movedQuotientImageEquiv ρ (⨆ i, L i)
        (subspaceCommutator ρ ⊤ (⨆ i, L i))).symm)

/-- The moved space of a conjugate is obtained by the original ambient action. -/
theorem moved_map_conjugate (K : Subgroup G) (g : G) :
    (subspaceCommutator ρ ⊤ K).map (ρ g) =
      subspaceCommutator ρ ⊤ (K.map (MulAut.conj g).toMonoidHom) := by
  have he : ∀ a v, ρ a (ρ g⁻¹ v) = ρ g⁻¹ (ρ ((MulAut.conj g) a) v) := by
    intro a v
    change ρ a (ρ g⁻¹ v) = ρ g⁻¹ (ρ (g * a * g⁻¹) v)
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply]
  have hh := subspaceCommutator_map_embedding ρ ρ (MulAut.conj g).toMonoidHom
    (ρ g⁻¹) he K ⊤
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr (ρ.apply_bijective g⁻¹).surjective] at hh
  rw [hh, ← Submodule.map_comp]
  have hc : (ρ g).comp (ρ g⁻¹) = LinearMap.id := by
    ext v
    exact ρ.self_inv_apply g v
  rw [hc, Submodule.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- Moving the literal fixed-space quotient is the image of the original moved space. -/
theorem moved_fixedQuotient (K : Subgroup G) [K.Normal] :
    subspaceCommutator (fixedQuotient ρ K) ⊤ K =
      (subspaceCommutator ρ ⊤ K).map (fixedSpace ρ K).mkQ := by
  have hh := subspaceCommutator_map_embedding (fixedQuotient ρ K) ρ (MonoidHom.id G)
    (fixedSpace ρ K).mkQ (fun _ _ => rfl) K ⊤
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
    Subgroup.map_id] at hh
  exact hh

/-- A permutation of the actual factors permutes their actual moved spaces. -/
theorem family_moved_permuted
    (hmoved : ∀ i, W i = subspaceCommutator ρ ⊤ (L i))
    {g : G} {i j : ι} (h : (L i).map (MulAut.conj g).toMonoidHom = L j) :
    (W i).map (ρ g) = W j := by
  rw [hmoved, moved_map_conjugate, h, hmoved]

set_option backward.isDefEq.respectTransparency false in
/-- The permutation persists on the literal ambient fixed-space quotient. -/
theorem family_central_images_permuted [(⨆ i, L i).Normal]
    (hmoved : ∀ i, W i = subspaceCommutator ρ ⊤ (L i))
    {g : G} {i j : ι} (h : (L i).map (MulAut.conj g).toMonoidHom = L j) :
    ((W i).map (fixedSpace ρ (⨆ j, L j)).mkQ).map (fixedQuotient ρ (⨆ j, L j) g) =
      (W j).map (fixedSpace ρ (⨆ j, L j)).mkQ := by
  rw [← Submodule.map_comp]
  have he : (fixedQuotient ρ (⨆ j, L j) g).comp (fixedSpace ρ (⨆ j, L j)).mkQ =
      (fixedSpace ρ (⨆ j, L j)).mkQ.comp (ρ g) := rfl
  rw [he, Submodule.map_comp, family_moved_permuted ρ L W hmoved h]

end Representation.BinaryOffender
