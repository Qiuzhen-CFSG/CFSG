module
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Fixed spaces, commutators, and socles through a centralizing supplement

If X=CQ and Q centralizes an elementary subgroup U, every subgroup of X
containing Q has representatives in C with exactly the same action on U.
A marking of the C-action consequently computes the original centralizers
and commutators. A surjective marking identifies the invariant-submodule
lattices and the literal socle for the full X-action.

The proofs retain the original subgroup maps and compare actual conjugates,
rather than replacing X by an abstract isomorphic group. These transports
are used by the Fano-core case of Aschbacher–Smith 13.4.14, printed p.911.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace Representation.BinaryConjugationCoordinates
private theorem orderIso_map_atoms {α β : Type*} [CompleteLattice α] [CompleteLattice β]
    (j : α ≃o β) : j (sSup {a : α | IsAtom a}) = sSup {b : β | IsAtom b} := by
  rw [j.map_sSup,←sSup_image]
  congr 1
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (j.isAtom_iff a).mpr ha
  · intro hb
    exact ⟨j.symm b,(j.symm.isAtom_iff b).mpr hb,j.apply_symm_apply b⟩

variable {G H M : Type*} [Group G] [Group H] [AddCommGroup M] [Module (ZMod 2) M]

/-- Each actor has the same action as a representative in the supplement. -/
theorem centralizing_supplement_representatives (X C Q U A : Subgroup G)
    (hCX : C ≤ X) (hQX : Q ≤ X) [(Q.subgroupOf X).Normal]
    (hgen : C ⊔ Q = X) (hQU : Q ≤ centralizer (U : Set G))
    (hAX : A ≤ X) (hQA : Q ≤ A) :
    ∀ a ∈ A, ∃ c : C, c.val ∈ A ∧ ∀ u : U,
      a * u.val * a⁻¹ = c.val * u.val * c.val⁻¹ := by
  have hg : C.subgroupOf X ⊔ Q.subgroupOf X = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCX,map_subgroupOf_eq_of_le hQX,
      ←MonoidHom.range_eq_map,range_subtype,hgen]
  intro a ha
  obtain ⟨c,hc,q,hq,hcq⟩ := mem_sup_of_normal_right.mp
    (hg ▸ mem_top (⟨a,hAX ha⟩ : X))
  have he : c.val * q.val = a := congrArg Subtype.val hcq
  have hca : c.val ∈ A := by
    rw [←mul_div_cancel_right c.val q.val,he]
    exact A.div_mem ha (hQA hq)
  refine ⟨⟨c.val,hc⟩,hca,fun u => ?_⟩
  rw [←he,mul_inv_rev]
  have hu : q.val * u.val * q.val⁻¹ = u.val :=
    mul_inv_eq_iff_eq_mul.mpr (hQU hq u.val u.property).symm
  calc
    c.val * q.val * u.val * (q.val⁻¹ * c.val⁻¹) =
        c.val * (q.val * u.val * q.val⁻¹) * c.val⁻¹ := by group
    _ = _ := by rw [hu]

variable (U C : Subgroup G) [IsElementaryAbelian 2 U]
    (hCU : C ≤ normalizer (U : Set G))
    (f : C →* H) (σ : Representation (ZMod 2) H M)
    (e : Representation.Equiv (σ.comp f) (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hCU))))

@[expose] def modelSpace (P : Subgroup G) : Submodule (ZMod 2) M :=
  (binarySpace (P.subgroupOf U)).comap e.toLinearMap

@[simp] theorem mem_modelSpace (P : Subgroup G) (v : M) :
    v ∈ modelSpace U C hCU f σ e P ↔ (e v).toMul.val ∈ P := Iff.rfl

theorem modelSpace_le_iff {P Q : Subgroup G} (hPU : P ≤ U) (_hQU : Q ≤ U) :
    modelSpace U C hCU f σ e P ≤ modelSpace U C hCU f σ e Q ↔ P ≤ Q := by
  constructor
  · intro h p hp
    obtain ⟨v,hv⟩ := e.surjective (Additive.ofMul ⟨p,hPU hp⟩)
    change e v = _ at hv
    have hp' : v ∈ modelSpace U C hCU f σ e P := by rw [mem_modelSpace,hv]; exact hp
    have hh := h hp'
    change (e v).toMul.val ∈ Q at hh
    rw [hv] at hh
    exact hh
  · intro h v hv
    exact h hv

private theorem equivariant_value (c : C) (v : M) :
    (e (σ (f c) v)).toMul.val = c.val * (e v).toMul.val * c.val⁻¹ := by
  exact congrArg (fun w : Additive U => w.toMul.val)
    (LinearMap.congr_fun (e.isIntertwining' c) v)

/-- Centralizers in the full actor are identified through its actual representatives. -/
theorem modelSpace_fixed (A : Subgroup G)
    (hreps : ∀ a ∈ A, ∃ c : C, c.val ∈ A ∧ ∀ u : U,
      a * u.val * a⁻¹ = c.val * u.val * c.val⁻¹) :
    modelSpace U C hCU f σ e (U ⊓ centralizer (A : Set G)) =
      fixedSpace σ ((A.subgroupOf C).map f) := by
  ext v
  constructor
  · intro hv
    rintro ⟨_,c,hc,rfl⟩
    change σ (f c) v = v
    apply e.toLinearEquiv.injective
    apply Additive.toMul.injective
    apply Subtype.ext
    change (e (σ (f c) v)).toMul.val = (e v).toMul.val
    rw [equivariant_value]
    exact mul_inv_eq_iff_eq_mul.mpr (hv.2 c.val hc)
  · intro hv
    refine ⟨(e v).toMul.property,?_⟩
    intro a ha
    obtain ⟨c,hc,he⟩ := hreps a ha
    have hh := hv ⟨f c,mem_map_of_mem f hc⟩
    change σ (f c) v = v at hh
    have hcfix : c.val * (e v).toMul.val * c.val⁻¹ = (e v).toMul.val := by
      rw [←equivariant_value,hh]
    exact mul_inv_eq_iff_eq_mul.mp ((he (e v).toMul).trans hcfix)

/-- Exact commutator coordinates, even when the original actor exceeds the marked supplement. -/
theorem modelSpace_commutator (Z A : Subgroup G) (hZU : Z ≤ U)
    (_hAU : A ≤ normalizer (U : Set G))
    (hreps : ∀ a ∈ A, ∃ c : C, c.val ∈ A ∧ ∀ u : U,
      a * u.val * a⁻¹ = c.val * u.val * c.val⁻¹) :
    modelSpace U C hCU f σ e ⁅Z,A⁆ =
      subspaceCommutator σ (modelSpace U C hCU f σ e Z) ((A.subgroupOf C).map f) := by
  let I := subspaceCommutator σ (modelSpace U C hCU f σ e Z) ((A.subgroupOf C).map f)
  let P : Subgroup G := (binarySubgroup (I.map e.toLinearMap)).map U.subtype
  have hp (v : M) : (e v).toMul.val ∈ P ↔ v ∈ I := by
    change U.subtype (e v).toMul ∈ (binarySubgroup (I.map e.toLinearMap)).map U.subtype ↔ _
    rw [mem_map_iff_mem U.subtype_injective]
    change e v ∈ I.map e.toLinearMap ↔ v ∈ I
    exact ⟨fun ⟨w,hw,he⟩ => (e.toLinearEquiv.injective he) ▸ hw,
      fun hv => ⟨v,hv,rfl⟩⟩
  have hcomm : ⁅Z,A⁆ ≤ P := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha z hz
    obtain ⟨c,hc,he⟩ := hreps a ha
    obtain ⟨v,hv⟩ := e.surjective (Additive.ofMul ⟨z,hZU hz⟩)
    change e v = _ at hv
    have hvZ : v ∈ modelSpace U C hCU f σ e Z := by rw [mem_modelSpace,hv]; exact hz
    have hd : σ (f c) v - v ∈ I :=
      Submodule.subset_span ⟨f c,mem_map_of_mem f hc,v,hvZ,rfl⟩
    have hh := (hp (σ (f c) v-v)).mpr hd
    rw [map_sub] at hh
    change (e (σ (f c) v)).toMul.val / (e v).toMul.val ∈ P at hh
    rw [div_eq_mul_inv] at hh
    rw [equivariant_value,hv] at hh
    have he' := he ⟨z,hZU hz⟩
    change a*z*a⁻¹ = c.val*z*c.val⁻¹ at he'
    change c.val*z*c.val⁻¹*z⁻¹ ∈ P at hh
    rw [←he'] at hh
    exact hh
  apply le_antisymm
  · intro v hv
    exact (hp v).mp (hcomm hv)
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨c,hc,rfl⟩,v,hv,rfl⟩
    change (e (σ (f c) v-v)).toMul.val ∈ ⁅Z,A⁆
    rw [map_sub]
    change (e (σ (f c) v)).toMul.val / (e v).toMul.val ∈ ⁅Z,A⁆
    rw [div_eq_mul_inv]
    rw [equivariant_value,commutator_comm]
    exact commutator_mem_commutator hc hv
end Representation.BinaryConjugationCoordinates

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryConjugationCoordinates
variable {G H M : Type*} [Group G] [Group H] [AddCommGroup M] [Module (ZMod 2) M]
variable (X U C : Subgroup G) [IsElementaryAbelian 2 U]
    (hXU : X ≤ normalizer (U : Set G)) (hCX : C ≤ X)
    (f : C →* H) (hf : Function.Surjective f) (σ : Representation (ZMod 2) H M)
    (e : Representation.Equiv (σ.comp f) (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (hCX.trans hXU)))))
    (hreps : ∀ x ∈ X, ∃ c : C, c.val ∈ X ∧ ∀ u : U,
      x * u.val * x⁻¹ = c.val * u.val * c.val⁻¹)

include hreps in
private theorem supplement_equivariant (x : X) : ∃ c : C, ∀ v : M,
    elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp (inclusion hXU)) x (e v) =
      e (σ (f c) v) := by
  obtain ⟨c,_,hc⟩ := hreps x.val x.property
  refine ⟨c,fun v => ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (hc (e v).toMul).trans (equivariant_value U C (hCX.trans hXU) f σ e c v).symm

/-- The marked component and full actor have the same invariant-submodule lattice. -/
@[expose] def supplementSubrepresentationEquiv : Subrepresentation σ ≃o
    Subrepresentation (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hXU))) where
  toFun N := {
    toSubmodule := N.toSubmodule.map e.toLinearMap
    apply_mem_toSubmodule x := by
      rintro _ ⟨v,hv,rfl⟩
      obtain ⟨c,hc⟩ := supplement_equivariant X U C hXU hCX f σ e hreps x
      change elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp (inclusion hXU)) x (e v) ∈ _
      rw [hc]
      exact ⟨σ (f c) v,N.apply_mem_toSubmodule (f c) hv,rfl⟩ }
  invFun N := {
    toSubmodule := N.toSubmodule.comap e.toLinearMap
    apply_mem_toSubmodule x := by
      intro v hv
      obtain ⟨c,rfl⟩ := hf x
      have hh := N.apply_mem_toSubmodule (⟨c.val,hCX c.property⟩ : X) hv
      have he : e (σ (f c) v) = elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion hXU)) ⟨c.val,hCX c.property⟩ (e v) :=
        LinearMap.congr_fun (e.isIntertwining' c) v
      change e (σ (f c) v) ∈ N
      rw [he]
      exact hh }
  left_inv N := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_map_eq_of_injective e.toLinearEquiv.injective _
  right_inv N := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective _
  map_rel_iff' := by
    intro N P
    exact Submodule.map_le_map_iff_of_injective e.toLinearEquiv.injective N.toSubmodule P.toSubmodule

/-- The transport identifies the literal span of simple submodules of the full actor. -/
theorem supplement_socle :
    (supplementSubrepresentationEquiv X U C hXU hCX f hf σ e hreps)
      (sSup {N : Subrepresentation σ | IsAtom N}) =
      sSup {N : Subrepresentation (elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion hXU))) | IsAtom N} := by
  exact orderIso_map_atoms
    (supplementSubrepresentationEquiv X U C hXU hCX f hf σ e hreps)
end Representation.BinaryConjugationCoordinates
