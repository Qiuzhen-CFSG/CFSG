module
public import Theory.Representation.PSL3Two.OrbitStabilizers
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Centralizers of natural binary three-space points

The stabilizer of every nonzero natural vector is S₄. Restrict the literal
component quotient to its ambient point centralizer and transport that
stabilizer identification. The resulting surjection has exactly the
restriction of the component two-core as kernel.

Source: the SL₃(2) point parabolic; used by Aschbacher–Smith 13.4.10(2),
printed p.908. The original consumer is ComponentLinearResidual.
-/

public noncomputable section
open Subgroup
namespace BinaryLinearThree

/-- The literal natural point-centralizer map has symmetric-four image and
kernel equal to the restriction of the component two-core. -/
theorem natural_point_centralizer
    {G : Type*} [_root_.Group G] [Finite G]
    (K U : Subgroup G) (hKU : K ≤ normalizer (U : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : U ≃* Multiplicative Vector)
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,hKU k.property⟩ v)).toAdd =
        W (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)
    (w : U) (hw : w ≠ 1) :
    ∃ f : (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = (K.pCoreIn 2).subgroupOf
        (K ⊓ centralizer ({w.val} : Set G)) := by
  let qK := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective qK := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let v := (e w).toAdd
  let P := OrbitStabilizers.natural v
  have hmem (k : K) : qK k ∈ P ↔ k.val ∈ centralizer ({w.val} : Set G) := by
    rw [OrbitStabilizers.mem_natural]
    change W (eK (QuotientGroup.mk' (pCore 2 K) k)) (e w).toAdd = (e w).toAdd ↔ _
    rw [←he k w,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    change k.val * w.val * k.val⁻¹ = w.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  have hv : v ≠ 0 := fun hh => hw (e.injective (hh.trans e.map_one.symm))
  let eP := OrbitStabilizers.naturalEquivSymmetric v hv
  let C := K ⊓ centralizer ({w.val} : Set G)
  let p : C →* P := (qK.comp (inclusion inf_le_left)).codRestrict _
    (fun c => (hmem (inclusion inf_le_left c)).mpr c.property.2)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨k,hk⟩ := hq x.val
    have hkc : k.val ∈ centralizer ({w.val} : Set G) :=
      (hmem k).mp (hk.symm ▸ x.property)
    exact ⟨⟨k.val,k.property,hkc⟩,Subtype.ext hk⟩
  refine ⟨eP.toMonoidHom.comp p,eP.surjective.comp hp,?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ eP.injective]
  ext c
  change p c = 1 ↔ c.val ∈ K.pCoreIn 2
  rw [Subtype.ext_iff]
  change eK (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left c)) = 1 ↔ _
  rw [eK.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff (inclusion inf_le_left c)).trans
    (mem_map_iff_mem K.subtype_injective).symm

end BinaryLinearThree

