module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Enumeration
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Model

/-!
# The model Sylow and binary kernel in the ambient group

The given embedding sends the concrete Sylow subgroup to an ambient Sylow:
both it and the original Sylow have order 128. Thus the concrete transfer
kernel becomes an index-two subgroup of an actual ambient Sylow without a
conjugacy choice. The remaining two inputs are a concrete subgroup assertion
and its transport to ambient normalizer actions.

This prepares the conditional exclusion for Huppert--Blackburn III,
XII.1.18(b), p.314. It does not discharge those two inputs.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (e : D.centralizer ≃* NonsplitModels.Second)

/-- Use the image of the fixed model Sylow directly; its order is the full
two-part of the ambient group. -/
@[expose] public noncomputable def ambientSylow : Sylow 2 G :=
  Sylow.ofCard (Model.sylowSubgroup.map (embedding D e)) (by
    rw [card_map_of_injective (embedding_injective D e), Model.sylowSubgroup_card,
      ← D.sylow.card_eq_multiplicity, D.sylow_card])

public theorem ambientSylow_coe : (ambientSylow D e : Subgroup G) =
    Model.sylowSubgroup.map (embedding D e) := rfl

public theorem ambientSylow_le : (ambientSylow D e : Subgroup G) ≤ D.centralizer :=
  (map_le_range (embedding D e) Model.sylowSubgroup).trans_eq (embedding_range D e)

public theorem ambientSylow_card : Nat.card (ambientSylow D e) = 128 := by
  change Nat.card (Model.sylowSubgroup.map (embedding D e)) = 128
  rw [card_map_of_injective (embedding_injective D e), Model.sylowSubgroup_card]

/-- The actual ambient image of the normal model kernel. No ambient normality
is asserted here. -/
@[expose] public def ambientTransferSubgroup : Subgroup G :=
  Model.transferSubgroup.map (embedding D e)

public theorem ambientTransferSubgroup_le :
    ambientTransferSubgroup D e ≤ (ambientSylow D e : Subgroup G) :=
  map_mono Model.transferSubgroup_le_sylow

omit [Finite G] in
public theorem ambientTransferSubgroup_card : Nat.card (ambientTransferSubgroup D e) = 64 := by
  rw [ambientTransferSubgroup, card_map_of_injective (embedding_injective D e),
    Model.transferSubgroup_card]

/-- The binary kernel is a subgroup of the ambient Sylow, with its actual inclusion. -/
@[expose] public noncomputable def ambientKernel : Subgroup (ambientSylow D e) :=
  (ambientTransferSubgroup D e).subgroupOf (ambientSylow D e : Subgroup G)

public theorem ambientKernel_index : (ambientKernel D e).index = 2 := by
  have hcard : Nat.card (ambientKernel D e) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe (ambientTransferSubgroup_le D e)).toEquiv).trans
      (ambientTransferSubgroup_card D e)
  have h := (ambientKernel D e).card_mul_index
  rw [hcard, ambientSylow_card D e] at h
  omega

/-- This equivalence retains the embedding on every group element. -/
@[expose] public noncomputable def sylowEquiv : Model.sylowSubgroup ≃* ambientSylow D e :=
  Model.sylowSubgroup.equivMapOfInjective (embedding D e) (embedding_injective D e)

public theorem sylowEquiv_apply (x : Model.sylowSubgroup) :
    (sylowEquiv D e x : G) = embedding D e x := rfl

public theorem sylowEquiv_mem_kernel (x : Model.sylowSubgroup) :
    sylowEquiv D e x ∈ ambientKernel D e ↔ (x : NonsplitModels.Second) ∈ Model.transferSubgroup := by
  change embedding D e x ∈ Model.transferSubgroup.map (embedding D e) ↔ _
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact embedding_injective D e hxy ▸ hy
  · intro hx
    exact mem_map_of_mem _ hx

public theorem ambientExceptionalSubgroup_le_sylow :
    ambientExceptionalSubgroup D e ≤ (ambientSylow D e : Subgroup G) :=
  map_mono Model.exceptionalSubgroup_le_sylow

omit [Finite G] in
/-- The model normality gives precisely the local normalizer containment
needed for the exceptional branch. -/
public theorem centralizer_le_normalizer_transfer :
    D.centralizer ≤ normalizer (ambientTransferSubgroup D e : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  rw [← embedding_range D e] at hg
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hx
  have hmem := (inferInstance : Model.transferSubgroup.Normal).conj_mem b hb a
  simpa only [ambientTransferSubgroup, map_mul, map_inv] using mem_map_of_mem (embedding D e) hmem

/-- Every conjugation by the actual involution centralizer preserves the
binary kernel. This handles an exceptional normalizer controlled by that group. -/
public theorem kernel_mem_of_local_conjugacy (g : G) (hg : g ∈ D.centralizer)
    (x y : ambientSylow D e) (hxy : g⁻¹ * (x : G) * g = (y : G)) :
    x ∈ ambientKernel D e ↔ y ∈ ambientKernel D e := by
  change (x : G) ∈ ambientTransferSubgroup D e ↔ (y : G) ∈ ambientTransferSubgroup D e
  have h := mem_normalizer_iff''.mp (centralizer_le_normalizer_transfer D e hg) (x : G)
  rwa [hxy] at h

/-- The same subgroup assertion after the actual model embedding. Proving its
transport from `CandidateProperty` is separate from the finite calculation. -/
@[expose] public def AmbientCandidateProperty : Prop :=
  ∀ U : Subgroup G, U ≤ (ambientSylow D e : Subgroup G) →
    ((ambientSylow D e : Subgroup G) ⊓ centralizer (U : Set G)) ≤ U →
    IntrinsicRadicalIn (ambientSylow D e : Subgroup G) U →
    ((ambientTransferSubgroup D e).subgroupOf U).Characteristic ∨
      U = ambientExceptionalSubgroup D e

/-- Characteristic intersections handle the ordinary candidates. The explicit
normalizer premise and local normality handle the exceptional candidate. -/
public theorem preservesKernel_of_ambient_candidates
    (hN : normalizer (ambientExceptionalSubgroup D e : Set G) ≤ D.centralizer)
    (hcandidates : AmbientCandidateProperty D e) :
    PreservesKernel (ambientSylow D e) (ambientKernel D e) := by
  intro U hUS _ hcent hrad g hg x y hx hxy
  rcases hcandidates U hUS hcent hrad with hchar | hU
  · let a : MulAut U := U.normalizerMonoidHom
      ⟨g⁻¹, (normalizer (U : Set G)).inv_mem hg⟩
    let xU : U := ⟨(x : G), hx⟩
    have ha : (a xU : G) = (y : G) := by
      change g⁻¹ * (x : G) * (g⁻¹)⁻¹ = (y : G)
      simpa only [inv_inv] using hxy
    have heq := congrArg (fun K : Subgroup U => xU ∈ K)
      (characteristic_iff_comap_eq.mp hchar a)
    change ((a xU : G) ∈ ambientTransferSubgroup D e) =
      ((x : G) ∈ ambientTransferSubgroup D e) at heq
    rw [ha] at heq
    exact Iff.of_eq heq.symm
  · subst U
    exact kernel_mem_of_local_conjugacy D e g (hN hg) x y hxy

/-- All remaining ambient work is concentrated in membership invariance of
the explicit kernel. The index and the nonsolvability inputs are discharged. -/
public theorem false_of_ambient_preservesKernel [IsSimpleGroup G]
    (h : PreservesKernel (ambientSylow D e) (ambientKernel D e)) : False :=
  false_of_preservesKernel (D.ambient_not_isSolvable) (ambientSylow D e)
    (ambientKernel D e) (ambientKernel_index D e) h

/-- Conditional assembly after the subgroup assertion has been transported.
The additional candidate premise remains a proof obligation for this task. -/
public theorem false_of_ambient_candidates [IsSimpleGroup G]
    (hN : normalizer (ambientExceptionalSubgroup D e : Set G) ≤ D.centralizer)
    (hcandidates : AmbientCandidateProperty D e) : False :=
  false_of_ambient_preservesKernel D e
    (preservesKernel_of_ambient_candidates D e hN hcandidates)

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer
