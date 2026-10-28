module
public import Theory.Representation.BinaryConjugationSection
public import Theory.SpecificGroups.SL3.BinaryPointStabilizer

/-!
# Point centralizers in a marked binary-three natural module

The literal coordinate map identifies an original point centralizer with
the preimage of its natural vector stabilizer, hence gives index seven.
Surjectivity of the coordinates also detects the full action kernel.
These statements keep the ambient conjugation action and the original
actor map, as used in Aschbacher--Smith 10.2.9, printed p.752.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {L W : Subgroup G}
    (q : L →* SL(3,ZMod 2))
    (s : BinaryConjugationSection L W ⊥ ((specialLinearNatural 3).comp q))

include s

private theorem coordinates_injective : Function.Injective s.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [s.kernel_eq,bot_subgroupOf]

theorem linearThree_centralizer_le_kernel {l : L}
    (hl : (l : G) ∈ centralizer (W : Set G)) : q l = 1 := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨w,hw⟩ := s.onto (Multiplicative.ofAdd v)
  have hc : (⟨(l : G)*w*(l : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized l.property) w).mp w.property⟩ : W) = w := by
    apply Subtype.ext
    change (l : G)*w*(l : G)⁻¹ = (w : G)
    rw [←hl w w.property,mul_inv_cancel_right]
  have he := s.equivariant l w
  rw [hc,hw] at he
  change v = specialLinearNatural 3 (q l) v at he
  rw [specialLinearNatural_apply] at he
  rw [Matrix.SpecialLinearGroup.toLin'_apply,Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.toLin'_apply,Matrix.toLin'_apply,Matrix.SpecialLinearGroup.coe_one,Matrix.one_mulVec]
  exact he.symm

theorem linearThree_pointCentralizer_eq_comap (w : W) :
    (L ⊓ centralizer ({(w : G)} : Set G)).subgroupOf L =
      (MulAction.stabilizer SL(3,ZMod 2) (s.coordinates w).toAdd).comap q := by
  ext l
  have hh := s.equivariant l w
  change (l : G) ∈ L ⊓ centralizer ({(w : G)} : Set G) ↔ _
  simp only [mem_inf,l.property,true_and,mem_centralizer_singleton_iff]
  change _ ↔ q l • (s.coordinates w).toAdd = (s.coordinates w).toAdd
  constructor
  · intro he
    have hc : (⟨(l : G)*w*(l : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalized l.property) w).mp w.property⟩ : W) = w := by
      apply Subtype.ext
      change (l : G)*w*(l : G)⁻¹ = (w : G)
      rw [he,mul_inv_cancel_right]
    rw [hc] at hh
    exact hh.symm
  · intro he
    change _ = q l • (s.coordinates w).toAdd at hh
    rw [he] at hh
    have hc := congrArg Subtype.val (coordinates_injective q s
      (Multiplicative.toAdd.injective hh))
    exact mul_inv_eq_iff_eq_mul.mp hc

theorem linearThree_pointCentralizer_index (hq : Function.Surjective q)
    (w : W) (hw : w ≠ 1) :
    ((L ⊓ centralizer ({(w : G)} : Set G)).subgroupOf L).index = 7 := by
  rw [linearThree_pointCentralizer_eq_comap q s,index_comap_of_surjective _ hq]
  apply BinaryLinear.NaturalThreePoint.stabilizer_index
  intro hz
  exact hw (coordinates_injective q s (hz.trans (map_one s.coordinates).symm))

end Representation.BinaryConjugationSection
