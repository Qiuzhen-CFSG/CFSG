module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate

/-!
# Transporting the singular fixed line of a Sylow subgroup

Once a standard Sylow subgroup fixes precisely zero and one singular diagonal
vector, conjugacy and inner transitivity on the singular diagonal class prove
that the nonzero vectors fixed by some Sylow subgroup are exactly that class.
The standard fixed-line calculation remains an explicit hypothesis here.

Source: Aschbacher–Smith, H.9.1(2), printed p.390. The existential quantifier
on the Sylow subgroup is essential.
-/

public section

open scoped Pointwise

namespace BinaryNaturalDual.ModelOrbits

private theorem fixes_sylow_conjugate {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (P : Sylow 2 G) (a : G) (v : W)
    (hv : ∀ b ∈ P, ρ b v = v) :
    ∀ b ∈ a • P, ρ b (ρ a v) = ρ a v := by
  intro b hb
  change b ∈ MulAut.conj a • (P : Set G) at hb
  obtain ⟨c, hc, rfl⟩ := Set.mem_smul_set.mp hb
  change ρ (a * c * a⁻¹) (ρ a v) = ρ a v
  rw [← Module.End.mul_apply, ← map_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [map_mul]
  change ρ a (ρ c v) = ρ a v
  rw [hv c hc]

/-- A standard Sylow fixed line and the diagonal orbit calculation give the
existential Sylow clause. The fixed-line hypothesis is an independent input,
not a claim that one Sylow fixes all singular diagonal vectors. -/
theorem singularDiagonal_iff_exists_sylow_fixed_of_standard {n : ℕ}
    (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    (P : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)))
    (z : CoordinateSpace n) (hz : IsSingularDiagonal z)
    (hP : ∀ w, (∀ a ∈ P, A.representation a w = w) ↔ w = 0 ∨ w = z)
    {v : CoordinateSpace n} (hv : v ≠ 0) :
    IsSingularDiagonal v ↔
      ∃ Q : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)),
        ∀ a ∈ Q, A.representation a v = v := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_injective
      (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
        (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n))
      DFunLike.coe_injective
  constructor
  · intro hvs
    obtain ⟨g, hg⟩ := exists_inner_eq_of_singularDiagonal A hz hvs
    refine ⟨MulAut.conj g • P, ?_⟩
    rw [← hg]
    exact fixes_sylow_conjugate A.representation P (MulAut.conj g) z
      ((hP z).mpr (Or.inr rfl))
  · rintro ⟨Q, hQ⟩
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
      (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) P Q
    have hfix := fixes_sylow_conjugate A.representation Q a⁻¹ v hQ
    rw [← ha, inv_smul_smul] at hfix
    have hback : A.representation a (A.representation a⁻¹ v) = v := by
      change (A.representation a * A.representation a⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have he : A.representation a⁻¹ v = z := by
      rcases (hP _).mp hfix with he | he
      · rw [he, map_zero] at hback
        exact (hv hback.symm).elim
      · exact he
    rw [he] at hback
    have hz0 : z ≠ 0 := fun he => hz.1 (congrArg Prod.fst he)
    rcases (coordinate_orbit_iff hn A hz0 hv).mp ⟨a, hback⟩ with hp | hs | hq
    · exact ((orbit_classes_disjoint z).1 hp.1 hz).elim
    · exact hs.2
    · exact ((orbit_classes_disjoint z).2.2 hz hq.1).elim

end BinaryNaturalDual.ModelOrbits
