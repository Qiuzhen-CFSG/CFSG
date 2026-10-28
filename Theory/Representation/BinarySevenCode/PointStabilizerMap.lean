module
public import Theory.Representation.BinarySevenCode.WeightFourPointMarking
public import Theory.Representation.BinarySevenCode.Normalizer

/-!
# Point-stabilizer quotients in a marked binary module

The original normalizer permutation map restricts onto each word stabilizer.
Its kernel is the original module centralizer, so the first isomorphism
theorem retains the literal ambient subgroup and quotient map. At weight
four, the support and complement give the marked S₄ × S₃ quotient.

Source application: Aschbacher--Smith, paragraph preceding 12.3.13, p.811.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinarySevenCode.NormalizerModel
open WeightTwoGeometry
variable {G : Type*} [Group G] {V : Subgroup G} (D : NormalizerModel V)

/-- The point centralizer inside the literal normalizer of the marked module. -/
def pointNormalizer (v : V) : Subgroup G :=
  normalizer (V : Set G) ⊓ centralizer ({(v : G)} : Set G)

/-- Restrict the original permutation map to the original point centralizer. -/
def pointPermutation (v : V) : pointNormalizer v →*
    symmetricStabilizer (D.coordinates v).toAdd :=
  (D.permutation.comp (inclusion inf_le_left)).codRestrict _ (fun n => by
    rw [mem_symmetricStabilizer]
    have hfix : V.normalizerMonoidHom ⟨n,n.property.1⟩ v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp n.property.2)
    have h := D.equivariant ⟨n,n.property.1⟩ v
    rw [hfix] at h
    exact h.symm)

theorem pointPermutation_apply (v : V) (n : pointNormalizer v) :
    (D.pointPermutation v n).val = D.permutation ⟨n,n.property.1⟩ := rfl

/-- Surjectivity on the module induces surjectivity on the exact word stabilizer. -/
theorem pointPermutation_surjective (hs : Function.Surjective D.permutation) (v : V) :
    Function.Surjective (D.pointPermutation v) := by
  intro a
  obtain ⟨n,hn⟩ := hs a.val
  have h := D.equivariant n v
  rw [hn,(mem_symmetricStabilizer _ _).mp a.property] at h
  have hfix := D.coordinates.injective (Multiplicative.toAdd.injective h)
  have hc : (n : G) ∈ centralizer ({(v : G)} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix))
  exact ⟨⟨n,n.property,hc⟩,Subtype.ext hn⟩

/-- The point action has exactly the original module centralizer as kernel. -/
theorem pointPermutation_ker (v : V) :
    (D.pointPermutation v).ker = (centralizer (V : Set G)).subgroupOf (pointNormalizer v) := by
  ext n
  constructor
  · intro hn
    have hperm : D.permutation ⟨n,n.property.1⟩ = 1 := congrArg Subtype.val hn
    intro x hx
    have he := D.equivariant ⟨n,n.property.1⟩ ⟨x,hx⟩
    rw [hperm,map_one] at he
    have hfix := D.coordinates.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix)).symm
  · intro hn
    apply Subtype.ext
    exact D.permutation_eq_one_of_centralizes_simplex ⟨n,n.property.1⟩
      (centralizer_le D.simplex_le hn)

instance pointNormalizer_centralizer_normal (v : V) :
    ((centralizer (V : Set G)).subgroupOf (pointNormalizer v)).Normal := by
  let f : pointNormalizer v →* normalizer (V : Set G) := inclusion inf_le_left
  exact inferInstanceAs (((centralizer (V : Set G)).subgroupOf
    (normalizer (V : Set G))).comap f).Normal

/-- The quotient retains the actual point subgroup and original centralizer. -/
def pointQuotientEquiv (hs : Function.Surjective D.permutation) (v : V) :
    (pointNormalizer v ⧸ (centralizer (V : Set G)).subgroupOf (pointNormalizer v)) ≃*
      symmetricStabilizer (D.coordinates v).toAdd :=
  (QuotientGroup.quotientMulEquivOfEq (D.pointPermutation_ker v).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.pointPermutation v)
      (D.pointPermutation_surjective hs v))

theorem pointQuotientEquiv_apply (hs : Function.Surjective D.permutation)
    (v : V) (n : pointNormalizer v) :
    D.pointQuotientEquiv hs v (QuotientGroup.mk'
      ((centralizer (V : Set G)).subgroupOf (pointNormalizer v)) n) =
        D.pointPermutation v n := rfl

/-- At weight four the same literal quotient has the source S₄ × S₃ marking. -/
def weightFourPointQuotientEquiv (hs : Function.Surjective D.permutation)
    (v : V) (hv : weight (D.coordinates v).toAdd.val = 4) :
    (pointNormalizer v ⧸ (centralizer (V : Set G)).subgroupOf (pointNormalizer v)) ≃*
      (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3)) :=
  (D.pointQuotientEquiv hs v).trans (WeightFourLocal.pointEquiv _ hv)

theorem weightFourPointQuotientEquiv_apply (hs : Function.Surjective D.permutation)
    (v : V) (hv : weight (D.coordinates v).toAdd.val = 4) (n : pointNormalizer v) :
    D.weightFourPointQuotientEquiv hs v hv (QuotientGroup.mk'
      ((centralizer (V : Set G)).subgroupOf (pointNormalizer v)) n) =
        WeightFourLocal.pointEquiv _ hv (D.pointPermutation v n) := rfl

end BinarySevenCode.NormalizerModel
