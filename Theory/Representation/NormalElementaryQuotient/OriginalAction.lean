module
public import Theory.Representation.NormalElementaryQuotient.FixedIndex
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Original conjugation on a normal elementary binary subgroup

Pull the existing faithful centralizer-quotient representation back to the
original actor. Its kernel is the literal ambient centralizer. Fixed vectors
and their indices retain the actual subgroup centralizers; the moved span is
the original commutator subgroup in additive coordinates. The pointwise
centralizer comparison lets a faithful moved-action theorem be applied without
removing global fixed attachments or replacing the original group.

Source application: Niles, *Pushing-up in finite groups* (1979), Lemmas2.9,
7.4 and7.6, printed pp.33,60–62.
-/

set_option backward.isDefEq.respectTransparency false

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {H : Type*} [Group H]
variable (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]

/-- Conjugation on the original normal elementary subgroup, with the original actor. -/
noncomputable def originalAction : Representation (ZMod 2) H (Additive V) :=
  (representation V (QuotientGroup.mk' (centralizer (V : Set H)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).comp
      (QuotientGroup.mk' (centralizer (V : Set H)))

theorem originalAction_apply (h : H) (v : Additive V) :
    ((originalAction V h v).toMul : H) = h * (v.toMul : H) * h⁻¹ :=
  by
  change ((representation V (QuotientGroup.mk' (centralizer (V : Set H)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (QuotientGroup.mk' (centralizer (V : Set H)) h) v).toMul : H) = _
  exact representation_apply V _ _ _ h v

/-- The section V/1 in its unchanged additive coordinates. -/
noncomputable def originalSection : BinaryConjugationSection (⊤ : Subgroup H) V ⊥
    ((originalAction V).comp (⊤ : Subgroup H).subtype) where
  section_le := le_top
  kernel_le := bot_le
  normalized := by rw [normalizer_eq_top]
  coordinates := {
    toFun := fun v => Multiplicative.ofAdd (Additive.ofMul v)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  onto := fun v => ⟨v.toAdd.toMul,rfl⟩
  kernel_eq := by
    ext x
    change x = 1 ↔ (x : H) = 1
    exact Subtype.val_inj.symm
  equivariant := by
    intro h v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (originalAction_apply V h (Additive.ofMul v)).symm

theorem originalAction_kernel : (originalAction V).ker = centralizer (V : Set H) := by
  ext h
  constructor
  · intro hh v hv
    have he := LinearMap.congr_fun hh (Additive.ofMul (⟨v,hv⟩ : V))
    have he' := congrArg (fun x : Additive V => (x.toMul : H)) he
    rw [originalAction_apply] at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro hh
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((originalAction V h v).toMul : H) = (v.toMul : H)
    rw [originalAction_apply, ← hh _ v.toMul.property, mul_inv_cancel_right]

theorem original_fixedSpace (A : Subgroup H) (v : Additive V) :
    v ∈ fixedSpace (originalAction V) A ↔ (v.toMul : H) ∈ centralizer (A : Set H) := by
  unfold originalAction
  rw [fixedSpace_comp_map]
  exact mem_fixedSpace_image V _ _ _ A v

theorem original_fixed_index [Finite V] (A : Subgroup H) :
    (V ⊓ centralizer (A : Set H)).relIndex V =
      2 ^ fixedCodim (originalAction V) A := by
  rw [inf_relIndex_left]
  unfold originalAction fixedCodim
  rw [fixedSpace_comp_map]
  exact centralizer_index_eq_fixedCodim V _ _ _ A

theorem original_moved_space (L : Subgroup H) :
    commutatorSpace V L = subspaceCommutator (originalAction V) ⊤ L := by
  unfold originalAction
  rw [subspaceCommutator_comp_map]
  exact commutatorSpace_eq V _ _ _ L

theorem original_moved_centralizer (L : Subgroup H) (h : H) :
    h ∈ centralizer ((⁅V,L⁆ : Subgroup H) : Set H) ↔
      ∀ w ∈ subspaceCommutator (originalAction V) ⊤ L, originalAction V h w = w := by
  rw [← original_moved_space]
  constructor
  · intro hh w hw
    apply Additive.toMul.injective
    apply Subtype.ext
    have hc : (w.toMul : H) * h = h * (w.toMul : H) := hh _ hw
    rw [originalAction_apply, ← hc, mul_inv_cancel_right]
  · intro hh w hw
    let v : Additive V := Additive.ofMul ⟨w,(commutator_le_left V L) hw⟩
    have hv : v ∈ commutatorSpace V L := hw
    have he := congrArg (fun x : Additive V => (x.toMul : H)) (hh v hv)
    rw [originalAction_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

end Representation.NormalElementaryQuotient
