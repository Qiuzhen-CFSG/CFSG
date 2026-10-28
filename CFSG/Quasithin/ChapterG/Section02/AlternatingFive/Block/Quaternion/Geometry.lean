module
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Centrality
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.KernelGeometry
public import Theory.Representation.BinaryPermutation.FiveLowRank

/-!
# Orthogonal action bounds for G.2.4(8)

An even permutation on the five-point core cannot have displacement rank one.
Consequently an actor fixing the seed hyperplane, or moving the four-space
only into the original point, is trivial in the starred quotient. These
calculations use the given coordinates and the actual quotient projection.
The final kernel lemma pulls that conclusion back across the supplied
collapse S=V_L.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Quaternion

private theorem even_low_rank (a : alternatingGroup (Fin 5))
    (h : Module.finrank (ZMod 2) (LinearMap.range
      (BinaryPermutation.coreRepresentation (Fin 5) a.val - LinearMap.id)) ≤ 1) : a = 1 := by
  rcases BinaryPermutation.FiveLowRank.low_rank a.val h with ha | ⟨i,j,hij,ha⟩
  · exact Subtype.ext ha
  · have hm := a.property
    rw [Equiv.Perm.mem_alternatingGroup, ha, Equiv.Perm.sign_swap hij] at hm
    exact False.elim ((by decide : (-1 : ℤˣ) ≠ 1) hm)

private abbrev Space := BinaryPermutation.core (Fin 5)
private noncomputable def subspace : Subgroup (Multiplicative Space) ≃o
    Submodule (ZMod 2) Space :=
  AddSubgroup.toSubgroup.symm.trans (AddSubgroup.toZModSubmodule 2)

private theorem subspace_card (A : Subgroup (Multiplicative Space)) :
    Nat.card A = 2 ^ Module.finrank (ZMod 2) (subspace A) := by
  have he : Nat.card A = Nat.card (subspace A) := rfl
  rw [he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- An even five-point permutation fixing an eight-subgroup of the core is trivial. -/
private theorem eq_one_of_fixes_eight (a : alternatingGroup (Fin 5))
    (A : Subgroup (Multiplicative Space)) (hA : Nat.card A = 8)
    (hfix : ∀ x ∈ A, BinaryPermutation.coreRepresentation (Fin 5) a.val x.toAdd = x.toAdd) :
    a = 1 := by
  let f := BinaryPermutation.coreRepresentation (Fin 5) a.val - LinearMap.id
  have hdim : Module.finrank (ZMod 2) (subspace A) = 3 := by
    have h := subspace_card A
    rw [hA] at h
    exact Nat.pow_right_injective (by decide : 1 < 2) h.symm
  have hle : subspace A ≤ f.ker := by
    intro x hx
    exact sub_eq_zero.mpr (hfix (Multiplicative.ofAdd x) hx)
  have hk : 3 ≤ Module.finrank (ZMod 2) f.ker := by
    simpa only [hdim] using Submodule.finrank_mono hle
  have hr := LinearMap.finrank_range_add_finrank_ker f
  norm_num only [BinaryPermutation.finrank_core, Fintype.card_fin] at hr
  apply even_low_rank a
  change Module.finrank (ZMod 2) f.range ≤ 1
  omega

/-- An even five-point permutation with displacement in a two-subgroup is trivial. -/
private theorem eq_one_of_displacement_two (a : alternatingGroup (Fin 5))
    (A : Subgroup (Multiplicative Space)) (hA : Nat.card A = 2)
    (hmove : ∀ x : Space,
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a.val x - x) ∈ A) :
    a = 1 := by
  have hdim : Module.finrank (ZMod 2) (subspace A) = 1 := by
    have h := subspace_card A
    rw [hA] at h
    exact Nat.pow_right_injective (by decide : 1 < 2) h.symm
  apply even_low_rank a
  have hle : LinearMap.range
      (BinaryPermutation.coreRepresentation (Fin 5) a.val - LinearMap.id) ≤ subspace A := by
    rintro _ ⟨x, rfl⟩
    exact hmove x
  exact (Submodule.finrank_mono hle).trans hdim.le

open Setup Block
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- The actual starred action is faithful on the elementary seed of order eight. -/
theorem starProjection_eq_one_of_centralizes_seed (d : Hypothesis D g)
    (c : EarlierStructure D g) (l : D.L)
    (hl : (l : G) ∈ centralizer (D.V : Set G)) : starProjection D l = 1 := by
  apply d.model.injective
  rw [map_one]
  let A := (D.V.subgroupOf D.VL).map d.coordinates.toMonoidHom
  have hV : D.V ≤ D.VL := c.orthogonal_intersection.symm ▸ inf_le_left
  have hc : Nat.card A = 8 := by
    rw [card_map_of_injective d.coordinates.injective,
      Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv, c.seed_card]
  apply eq_one_of_fixes_eight _ A hc
  rintro _ ⟨v, hv, rfl⟩
  have he := d.equivariant l v
  have hconj : (⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_VL D l.property) v).mp v.property⟩ : D.VL) = v := by
    apply Subtype.ext
    change (l : G) * v * (l : G)⁻¹ = v
    rw [← hl v hv, mul_inv_cancel_right]
  rw [hconj] at he
  exact (congrArg Multiplicative.toAdd he).symm

/-- Displacement into the original point forces the actual starred actor to vanish. -/
theorem starProjection_eq_one_of_commutator_point (d : Hypothesis D g) (l : D.L)
    (hl : ∀ v ∈ D.VL, ⁅(l : G), v⁆ ∈ D.V₁) : starProjection D l = 1 := by
  apply d.model.injective
  rw [map_one]
  let A := (D.V₁.subgroupOf D.VL).map d.coordinates.toMonoidHom
  have hpoint : D.V₁ ≤ D.VL := le_conjugateSpanBy _ _
  have hc : Nat.card A = 2 := by
    rw [card_map_of_injective d.coordinates.injective,
      Nat.card_congr (subgroupOfEquivOfLe hpoint).toEquiv,
      d.point_card]
  apply eq_one_of_displacement_two _ A hc
  intro x
  obtain ⟨v, hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd x)
  let v' : D.VL := ⟨(l : G) * v * (l : G)⁻¹,
    (mem_normalizer_iff.mp (L_normalizes_VL D l.property) v).mp v.property⟩
  refine ⟨v' * v⁻¹, ?_, ?_⟩
  · exact hl v v.property
  · change d.coordinates (v' * v⁻¹) = _
    rw [map_mul, map_inv, show d.coordinates v' = _ from d.equivariant l v, hv]
    change _ + -x = _ - x
    rw [sub_eq_add_neg]
    rfl

omit [Finite G] in
/-- The literal star kernel inside I becomes V_L after the given collapse. -/
theorem mem_first_of_starProjection_eq_one (c : EarlierStructure D g)
    (hS : D.S g = D.VL) (l : D.L) (hl : starProjection D l = 1) : (l : G) ∈ D.VL := by
  rw [← hS, c.star_kernel]
  refine ⟨c.L_le_I l.property, ?_⟩
  let l' : D.LT := ⟨l, (show D.L ≤ D.LT from le_sup_left) l.property⟩
  have hq : QuotientGroup.mk' (pCore 2 D.LT) l' = 1 := congrArg Subtype.val hl
  exact ⟨l', (QuotientGroup.eq_one_iff l').mp hq, rfl⟩

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Quaternion
