module
public import Theory.Representation.BinaryOffender.IrreducibleFixedQuotient
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import Theory.Representation.BinaryOffender.TwoSectionBudget
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.SubrepresentationLattice

/-!
# A strict section bound makes a fully moved central quotient irreducible

For a perfect normal subgroup K, quotienting by C_V(K) leaves no K-fixed
vectors. If V=[V,K], every proper quotient is noncentral. A strict lower
bound exceeding the same actor's rank on every noncentral section therefore
allows only one irreducible section when the whole displacement is at most
twice that rank. When an elementary quadratic subgroup supplements a
centerless quasisimple K, the homogeneous-orbit theorem makes this section
irreducible also on K. The resulting whole space belongs to Irr⁺(K,V).

The strict bound is a general explicit input; the native M22 application
proves it using absence of faithful FF-modules. No splitting of V is used.
Source: Aschbacher–Smith, A.1.40 and the section argument of F.9.18(7),
printed pp.31,326, as used in 13.8.21(2), p.956.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
universe u v
variable {D : Type u} [Group D] {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) D E) (K : Subgroup D) [K.Normal] [Group.IsPerfect K]

theorem fixedQuotient_fixedSpace_eq_bot : fixedSpace (fixedQuotient ρ K) K = ⊥ := by
  let q := (fixedSpace ρ K).mkQ
  let W := (fixedSpace (fixedQuotient ρ K) K).comap q
  have hs : K ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    intro k hk w hw
    change q (ρ k w) ∈ fixedSpace (fixedQuotient ρ K) K
    have he : q (ρ k w) = q w := hw ⟨k,hk⟩
    rw [he]
    exact hw
  have hc : subspaceCommutator ρ W K ≤ fixedSpace ρ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,w,hw,rfl⟩
    exact (Submodule.Quotient.eq _).mp (hw ⟨k,hk⟩)
  have hW := le_fixedSpace_of_commutator_le_fixedSpace ρ K W hs hc
  apply bot_unique
  intro v hv
  obtain ⟨w,rfl⟩ := (fixedSpace ρ K).mkQ_surjective v
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hW hv)

omit [K.Normal] [Group.IsPerfect K] in
theorem quotient_fully_moved (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    (W : Subrepresentation ρ) :
    subspaceCommutator W.quotientRepresentation ⊤ K = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  obtain ⟨w,rfl⟩ := W.toSubmodule.mkQ_surjective v
  have hw : w ∈ subspaceCommutator ρ ⊤ K := by rw [hfull]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k,hk,y,_,rfl⟩ := hx
    exact Submodule.subset_span ⟨k,hk,W.toSubmodule.mkQ y,Submodule.mem_top,rfl⟩
  | zero => exact (subspaceCommutator W.quotientRepresentation ⊤ K).zero_mem
  | add x y _ _ hx hy => exact (subspaceCommutator W.quotientRepresentation ⊤ K).add_mem hx hy
  | smul a x _ hx => exact (subspaceCommutator W.quotientRepresentation ⊤ K).smul_mem a hx

omit [K.Normal] [Group.IsPerfect K] in
theorem noncentral_of_fully_moved [Nontrivial E]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤) : ¬ K ≤ ρ.ker := by
  intro hk
  have hz : subspaceCommutator ρ ⊤ K = ⊥ :=
    (subspaceCommutator_eq_bot_iff ρ ⊤ K).mpr (by
      intro x _ k
      exact LinearMap.congr_fun (hk k.property) x)
  exact top_ne_bot (hfull.symm.trans hz)

omit [K.Normal] [Group.IsPerfect K] in
theorem irreducible_of_noFF_sections [Finite E] [Nontrivial E]
    (A : Subgroup D)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfix : fixedSpace ρ K = ⊥)
    (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    (hstrict : ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (σ : Representation (ZMod 2) D W), ¬ K ≤ σ.ker → rank A < fixedCodim σ A) :
    IsIrreducible ρ := by
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  obtain ⟨I,hI,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
  have hnI : ¬ K ≤ I.toRepresentation.ker := by
    intro hk
    apply hI.ne_bot
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro x hx
    have hf : x ∈ fixedSpace ρ K := fun k =>
      congrArg Subtype.val (LinearMap.congr_fun (hk k.property) (⟨x,hx⟩ : I))
    exact hfix ▸ hf
  have hi : I = ⊤ := by
    by_contra hne
    have hsub : I.toSubmodule ≠ ⊤ := fun he => hne (Subrepresentation.toSubmodule_injective he)
    let : Finite (E ⧸ I.toSubmodule) := Finite.of_surjective _ I.toSubmodule.mkQ_surjective
    let : Nontrivial (E ⧸ I.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hsub
    have hfullQ := quotient_fully_moved ρ K hfull I
    have hnQ := noncentral_of_fully_moved I.quotientRepresentation K hfullQ
    have h₁ := hstrict I.toSubmodule I.toRepresentation hnI
    have h₂ := hstrict _ I.quotientRepresentation hnQ
    have hsum := fixedCodim_quotient_add_subrepresentation_le ρ I A
    omega
  have hirr := (Subrepresentation.irreducible_iff_isAtom I).mpr hI
  subst I
  let e : (⊤ : Subrepresentation ρ).toRepresentation ≃ₗ ρ :=
    { Submodule.topEquiv with isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  exact e.irreducible_euqiv.mp hirr

omit [Group.IsPerfect K] in
theorem top_isIrrPlus_of_strict_sections [Finite D] [Finite E]
    [Theory.GroupTheory.IsQuasisimple K]
    (hz : center K = ⊥) (A : Subgroup D) (hgen : K ⊔ A = ⊤)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (hfull : subspaceCommutator ρ ⊤ K = ⊤) (hn : ¬ K ≤ ρ.ker)
    (hstrict : ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (σ : Representation (ZMod 2) D W), ¬ K ≤ σ.ker → rank A < fixedCodim σ A) :
    IsIrrPlus ρ K ⊤ := by
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let C := fixedSubrepresentation ρ K
  let σ := fixedQuotient ρ K
  let : Finite (E ⧸ C.toSubmodule) := Finite.of_surjective _ C.toSubmodule.mkQ_surjective
  have hC : fixedSpace ρ K ≠ ⊤ := by
    intro he
    apply hn
    intro k hk
    ext v
    exact (show v ∈ fixedSpace ρ K from he.symm ▸ Submodule.mem_top) ⟨k,hk⟩
  let : Nontrivial (E ⧸ C.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hC
  have hboundQ : fixedCodim σ A ≤ 2 * rank A :=
    (fixedCodim_le_of_equivariant_surjection ρ σ C.toSubmodule.mkQ
      C.toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans hbound
  have hfullQ := quotient_fully_moved ρ K hfull C
  have hi : IsIrreducible σ := irreducible_of_noFF_sections σ K A hboundQ
    (fixedQuotient_fixedSpace_eq_bot ρ K) hfullQ hstrict
  let : Nontrivial (E ⧸ fixedSpace ρ K) := Submodule.Quotient.nontrivial_iff.mpr hC
  have hnQ : ¬ (⊤ : Submodule (ZMod 2) (E ⧸ fixedSpace ρ K)) ≤ fixedSpace σ K := by
    rw [fixedQuotient_fixedSpace_eq_bot]
    exact not_le_of_gt bot_lt_top
  have hirr := component_irreducible_of_quadratic_supplement σ K A hz hgen hA
    (quadratic_of_equivariant_surjection ρ σ C.toSubmodule.mkQ
      C.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hq) hboundQ hAC hi hnQ
  have hs : K ≤ subspaceStabilizer ρ ⊤ := le_subspaceStabilizer ρ ⊤ (by simp)
  refine ⟨hs,hfull,?_⟩
  exact irreducible_of_surjective_equivariant _ _ (MonoidHom.id K) Function.surjective_id
    (topCentralQuotientEquiv ρ K) (fun a v => topCentralQuotientEquiv_intertwines ρ K hs a v) hirr
end Representation.BinaryOffender
