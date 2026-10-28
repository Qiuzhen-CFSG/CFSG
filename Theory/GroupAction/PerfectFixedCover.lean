module

public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.SolvableResidual

/-!
# Perfect fixed-point covers modulo a solvable coprime kernel

An action fixing a coset modulo an invariant solvable subgroup of coprime
order admits a fixed representative in that coset. Its displacement is a
nonabelian cocycle; the coprime cocycle theorem makes it a coboundary.
If the entire quotient is fixed and the ambient group is perfect, the
solvable residual of the fixed subgroup still surjects onto the quotient.
Thus that residual and the kernel give a literal set-product factorization.

Only the kernel's order must be coprime to the actor's order. The ambient
group need not be solvable or have coprime order. This is the finite-group
argument in Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 4.4.5, printed p.620.
-/

public section
namespace Theory.GroupAction
open Subgroup
open scoped Pointwise

variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
  [MulDistribMulAction A G]

/-- A fixed coset modulo a solvable coprime invariant subgroup has a fixed representative. -/
theorem exists_fixed_mul_of_solvable_coprime_displacement (N : Subgroup G) [IsInvariant A G N]
    (hsolv : Group.IsSolvable N) (hcop : Nat.Coprime (Nat.card A) (Nat.card N))
    (g : G) (hg : ∀ a : A, g⁻¹ * (a • g) ∈ N) :
    ∃ n : N, g * (n : G) ∈ FixedPoints.subgroup A G := by
  let c : A → N := fun a => ⟨g⁻¹ * (a • g), hg a⟩
  have hc : ∀ a b : A, c (a * b) = c a * (a • c b) := by
    intro a b
    apply Subtype.ext
    change g⁻¹ * ((a * b) • g) =
      (g⁻¹ * (a • g)) * (a • (g⁻¹ * (b • g)))
    simp only [mul_smul, smul_mul', smul_inv']
    group
  obtain ⟨n, hn⟩ := exists_principal_cocycle_of_solvable_coprime hsolv hcop c hc
  refine ⟨n, ?_⟩
  intro a
  have he : g⁻¹ * (a • g) = (n : G) * (a • (n : G))⁻¹ :=
    congrArg Subtype.val (hn a)
  calc
    a • (g * (n : G)) = (a • g) * (a • (n : G)) := smul_mul' a g n
    _ = (g * (g⁻¹ * (a • g))) * (a • (n : G)) := by group
    _ = g * (n : G) := by rw [he]; group

/-- A fixed quotient by a coprime solvable kernel is covered by fixed points. -/
theorem fixedPoint_quotient_surjective_of_solvable_coprime_displacement (N : Subgroup G) [N.Normal] [IsInvariant A G N]
    (hsolv : Group.IsSolvable N) (hcop : Nat.Coprime (Nat.card A) (Nat.card N))
    (htriv : ∀ a : A, ∀ g : G, g⁻¹ * (a • g) ∈ N) :
    Function.Surjective ((QuotientGroup.mk' N).comp (FixedPoints.subgroup A G).subtype) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  obtain ⟨n, hn⟩ := exists_fixed_mul_of_solvable_coprime_displacement N hsolv hcop g (fun a => htriv a g)
  refine ⟨⟨g * n, hn⟩, ?_⟩
  change QuotientGroup.mk' N (g * n) = QuotientGroup.mk' N g
  have hnq : QuotientGroup.mk' N (n : G) = 1 := (QuotientGroup.eq_one_iff (n : G)).mpr n.property
  rw [map_mul, hnq, mul_one]

/-- The perfect residual of the fixed subgroup still covers a perfect ambient group. -/
theorem solvableResidual_fixedPoints_mul_eq_univ [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] [IsInvariant A G N]
    (hsolv : Group.IsSolvable N) (hcop : Nat.Coprime (Nat.card A) (Nat.card N))
    (htriv : ∀ a : A, ∀ g : G, g⁻¹ * (a • g) ∈ N) :
    ((solvableResidual (FixedPoints.subgroup A G)).map
      (FixedPoints.subgroup A G).subtype : Set G) * (N : Set G) = Set.univ := by
  let C := FixedPoints.subgroup A G
  let q := QuotientGroup.mk' N
  let f := q.comp C.subtype
  let : Group.IsPerfect (G ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hm : ((solvableResidual C).map C.subtype).map q = ⊤ := by
    rw [map_map, map_solvableResidual_eq f (fixedPoint_quotient_surjective_of_solvable_coprime_displacement N hsolv hcop htriv),
      solvableResidual_eq_top]
  have hc := congrArg (Subgroup.comap q) hm
  rw [comap_map_eq, QuotientGroup.ker_mk', comap_top] at hc
  rw [← mul_normal, hc]
  rfl

end Theory.GroupAction
