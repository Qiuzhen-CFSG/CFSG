module
public import Theory.Representation.BinaryPermutation.SixNaturalPoint
public import Theory.Representation.BinaryPermutation.SixNaturalCoverPoint
public import Theory.Representation.BinaryPermutation.SixCoreResidualMovement
public import Theory.Representation.BinaryPermutation.CoreFixedLine
/-!
# The marked natural A₆ point-centralizer quotient

A lift of a nonzero natural vector to the augmentation core is nonconstant.
Its S₄ stabilizer lies in the natural stabilizer; both have order 24, so
these are the same subgroup. Pulling this stabilizer back along the literal
component quotient gives a surjection C_K(w) → S₄ with kernel C_K(w) ∩ O₂(K).
This preserves the original vector and conjugation coordinates.

The actual reciprocal component application is Chapter13,
FixedCoreSource/Nonsolvable/ReciprocalSix, in the natural-row exclusion of
Aschbacher–Smith 13.4.15, printed p.912, using B.3.1–4, pp.83–85.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation

private theorem six_natural_stabilizer (w : natural (Fin 6)) (hw : w ≠ 0) :
    Nonempty (SixNaturalCoverPoint.point w ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨v,hv⟩ := coreToNatural_surjective w
  have hnf : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a v = v := by
    intro hh
    have hc := (core_fixed_iff_constant (by simp) v).mp hh
    have hz : coreToNatural (Fin 6) v = 0 := by
      rw [←Subtype.val_inj]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hc
    exact hw (hv.symm.trans hz)
  obtain ⟨e⟩ := SixCoreResidualMovement.stabilizer_equiv v hnf
  have hle : SixCoreResidualMovement.S v ≤ SixNaturalCoverPoint.point w := by
    intro a ha
    change alternatingNaturalRepresentation (Fin 6) a w = w
    rw [←hv]
    change naturalRepresentation (Fin 6) a.val (coreToNatural (Fin 6) v) = _
    rw [←coreToNatural_equivariant]
    exact congrArg (coreToNatural (Fin 6)) ha
  have hc : Nat.card (SixCoreResidualMovement.S v) = 24 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  have heq : SixCoreResidualMovement.S v = SixNaturalCoverPoint.point w :=
    eq_of_le_of_card_ge hle (by rw [hc,SixNaturalCoverPoint.point_card w hw])
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans e⟩

variable {G : Type*} [Group G]
/-- The literal point centralizer of a marked natural A₆ module maps onto
S₄ with precisely the original component two-core as kernel. -/
theorem six_natural_point_centralizer (K U : Subgroup G)
    (hn : K ≤ normalizer (U : Set G))
    (q : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (e : U ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,hn k.property⟩ v)).toAdd =
        alternatingNaturalRepresentation (Fin 6) (q (QuotientGroup.mk' (pCore 2 K) k))
          (e v).toAdd)
    (w : U) (hw : w ≠ 1) :
    ∃ f : (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧
        f.ker = (K.pCoreIn 2).subgroupOf (K ⊓ centralizer ({w.val} : Set G)) := by
  let S := SixNaturalCoverPoint.point (e w).toAdd
  let C := K ⊓ centralizer ({w.val} : Set G)
  let g := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hg : Function.Surjective g := q.surjective.comp (QuotientGroup.mk'_surjective _)
  have hmem (k : K) : g k ∈ S ↔ k.val ∈ centralizer ({w.val} : Set G) := by
    change alternatingNaturalRepresentation (Fin 6) (q (QuotientGroup.mk' (pCore 2 K) k)) (e w).toAdd = (e w).toAdd ↔ _
    rw [←he k w,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    change k.val * w.val * k.val⁻¹ = w.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  let p : C →* S := (g.comp (inclusion inf_le_left)).codRestrict S
    (fun x => (hmem (inclusion inf_le_left x)).mpr x.property.2)
  have hp : Function.Surjective p := by
    intro a
    obtain ⟨k,hk⟩ := hg a.val
    exact ⟨⟨k.val,k.property,(hmem k).mp (hk ▸ a.property)⟩,Subtype.ext hk⟩
  have hpk : p.ker = (K.pCoreIn 2).subgroupOf C := by
    ext x
    change p x = 1 ↔ x.val ∈ K.pCoreIn 2
    rw [Subtype.ext_iff]
    change g (inclusion inf_le_left x) = 1 ↔ x.val ∈ K.pCoreIn 2
    change q (QuotientGroup.mk' (pCore 2 K) _) = 1 ↔ _
    rw [q.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff (inclusion inf_le_left x)).trans
      (mem_map_iff_mem K.subtype_injective).symm
  obtain ⟨a⟩ := six_natural_stabilizer (e w).toAdd
    (fun hh => hw (e.injective (hh.trans e.map_one.symm)))
  exact ⟨a.toMonoidHom.comp p,a.surjective.comp hp,
    (MonoidHom.ker_comp_of_injective _ _ a.injective).trans hpk⟩
end BinaryPermutation
