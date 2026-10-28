module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum

/-!
# Cubic conjugacy and an embedded pentagon group in A₅

Order-three subgroups of A₅ are Sylow subgroups, so Sylow conjugacy gives
actual elements transporting them. The even permutations of a pentagon give
an injective homomorphism from `DihedralGroup 5`; its ten normal forms and
multiplication are checked in the kernel. The image and its embedding are
retained when transporting to any subgroup isomorphic to A₅.

These elementary facts are used in Aschbacher, *Sporadic Groups* (1994),
47.10, pp.266–267. The source application is in
`J2Recognition.SourceLocal.AlternatingFiveGeometry`.
-/

public section

open Subgroup
open scoped Pointwise
namespace alternatingGroup.FiveLocalGeometry

abbrev A5 := alternatingGroup (Fin 5)

theorem card : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- All cubic subgroups of A₅ are Sylow subgroups. -/
noncomputable def cubicSylow {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 3) : Sylow 3 H :=
  Sylow.ofCard P (by rw [hP, Nat.card_congr e.toEquiv, card]; decide +kernel)

theorem cubic_conjugate {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P Q : Subgroup H) (hP : Nat.card P = 3)
    (hQ : Nat.card Q = 3) :
    ∃ g : H, P.map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (cubicSylow e P hP) (cubicSylow e Q hQ)
  refine ⟨g, ?_⟩
  have he := congrArg (fun S : Sylow 3 H => (S : Subgroup H)) hg
  exact he

private def rotation : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
private def reflection : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 2 3

private theorem rotation_even : rotation ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private theorem reflection_even : reflection ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private def dihedralPerm : DihedralGroup 5 → Equiv.Perm (Fin 5)
  | .r i => rotation ^ i.val
  | .sr i => reflection * rotation ^ i.val

private theorem dihedralPerm_even (d : DihedralGroup 5) :
    dihedralPerm d ∈ alternatingGroup (Fin 5) := by
  cases d with
  | r i => exact pow_mem rotation_even i.val
  | sr i => exact mul_mem reflection_even (pow_mem rotation_even i.val)

private theorem dihedralPerm_mul : ∀ d e : DihedralGroup 5,
    dihedralPerm (d * e) = dihedralPerm d * dihedralPerm e := by decide +kernel

/-- The rotations and reflections of a pentagon act by even permutations. -/
def dihedralHom : DihedralGroup 5 →* A5 where
  toFun d := ⟨dihedralPerm d, dihedralPerm_even d⟩
  map_one' := Subtype.ext (by decide +kernel)
  map_mul' d e := Subtype.ext (dihedralPerm_mul d e)

theorem dihedralHom_injective : Function.Injective dihedralHom := by
  have hi : Function.Injective (fun d : DihedralGroup 5 =>
      (dihedralPerm d 0, dihedralPerm d 1)) := by decide +kernel
  intro d e h
  apply hi
  exact congrArg (fun g : A5 => (g.val 0, g.val 1)) h

variable {G : Type*} [Group G]

/-- Transport the marked pentagon action to any actual A₅ subgroup. -/
def dihedralEmbedding (F : Subgroup G) (e : F ≃* A5) : DihedralGroup 5 →* G :=
  F.subtype.comp (e.symm.toMonoidHom.comp dihedralHom)

theorem dihedralEmbedding_injective (F : Subgroup G) (e : F ≃* A5) :
    Function.Injective (dihedralEmbedding F e) :=
  F.subtype_injective.comp (e.symm.injective.comp dihedralHom_injective)

theorem dihedralEmbedding_range_le (F : Subgroup G) (e : F ≃* A5) :
    (dihedralEmbedding F e).range ≤ F := by
  rintro _ ⟨d, rfl⟩
  exact (e.symm (dihedralHom d)).property

noncomputable def dihedralEmbedding_range_equiv (F : Subgroup G) (e : F ≃* A5) :
    (dihedralEmbedding F e).range ≃* DihedralGroup 5 :=
  (MonoidHom.ofInjective (dihedralEmbedding_injective F e)).symm

theorem exists_dihedral (F : Subgroup G) (e : F ≃* A5) :
    ∃ B : Subgroup G, B ≤ F ∧ Nonempty (B ≃* DihedralGroup 5) :=
  ⟨(dihedralEmbedding F e).range, dihedralEmbedding_range_le F e,
    ⟨dihedralEmbedding_range_equiv F e⟩⟩


private def cubic : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel⟩
private def cubicReflection : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel⟩

private theorem cubic_order : orderOf cubic = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem cubicReflection_conj :
    cubicReflection * cubic * cubicReflection⁻¹ = cubic⁻¹ := by decide +kernel

private theorem cubicReflection_normalizes :
    cubicReflection ∈ normalizer (zpowers cubic : Set A5) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers (cubicReflection * cubic * cubicReflection⁻¹) = _
  rw [cubicReflection_conj, zpowers_inv]

private theorem cubicReflection_moves : cubicReflection * cubic ≠ cubic * cubicReflection := by
  decide +kernel

/-- A normalizing element acts nontrivially on every cubic subgroup of A₅. -/
theorem exists_noncommuting_normalizer {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 3) :
    ∃ t : H, t ∈ normalizer (P : Set H) ∧ ∃ x ∈ P, t * x ≠ x * t := by
  have hPe : Nat.card (P.map e.toMonoidHom) = 3 := by
    rw [card_map_of_injective e.injective, hP]
  obtain ⟨g, hg⟩ := cubic_conjugate (MulEquiv.refl A5) (P.map e.toMonoidHom)
    (zpowers cubic) hPe (by rw [Nat.card_zpowers, cubic_order])
  let a : H ≃* A5 := e.trans (MulAut.conj g)
  have ha : P.map a.toMonoidHom = zpowers cubic := by
    rw [map_map] at hg
    exact hg
  have ht : a.symm cubicReflection ∈ normalizer (P : Set H) := by
    have hs := cubicReflection_normalizes
    rw [← ha, ← map_equiv_normalizer_eq P a, mem_map_equiv] at hs
    exact hs
  have hx : a.symm cubic ∈ P := by
    have hx := mem_zpowers cubic
    rw [← ha, mem_map_equiv] at hx
    exact hx
  refine ⟨a.symm cubicReflection, ht, a.symm cubic, hx, ?_⟩
  intro hc
  apply cubicReflection_moves
  have hm := congrArg a hc
  simpa only [map_mul, MulEquiv.apply_symm_apply] using hm

end alternatingGroup.FiveLocalGeometry
