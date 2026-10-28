module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Basic

/-!
# Scalar and coefficient normalizers

Every nontrivial scalar subgroup has zero as its unique fixed point.
Its normalizer must preserve that point. In contrast, a coefficient subgroup
fixes both zero and one. If an element of the zero stabilizer normalizes it,
uniqueness of scalar-times-coefficient coordinates shows that conjugation is
just conjugation by the coefficient part, which is trivial since Γ is cyclic.

These statements supply the two stabilizer-normalizer comparisons in GLS,
Volume 4, Chapter 1, Lemma 3.9, `refs/KGroup/GLS4/Chapter1.tex`, lines 437–450.
They retain the ambient subgroups and do not assert transfer control.
-/

public section

open scoped IsMulCommutative
namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Field F] [MulAction X F] [FaithfulSMul X F]
variable (c : Coordinates X F)
include c

/-- A nontrivial scalar subgroup fixes only zero, so its entire ambient
normalizer lies in the zero stabilizer. -/
theorem scalar_normalizer_le_stabilizer {Z : Subgroup X}
    (hZ : Z ≤ c.scalarSubgroup) (hne : Z ≠ ⊥) :
    Subgroup.normalizer (Z : Set X) ≤ stabilizer X (0 : F) := by
  obtain ⟨z, hz, hz1⟩ := (Z.bot_or_exists_ne_one).resolve_left hne
  intro g hg
  have hz' : g * z * g⁻¹ ∈ c.scalarSubgroup :=
    hZ ((Subgroup.mem_normalizer_iff.mp hg z).mp hz)
  obtain ⟨a, ha⟩ := hz'
  have ha1 : a ≠ 1 := by
    intro ha1
    have h : g * z * g⁻¹ = 1 := by simpa [ha1] using ha.symm
    apply hz1
    have h' := congrArg (fun x : X => g⁻¹ * x * g) h
    simpa [mul_assoc] using h'
  have hz0 : z • (0 : F) = 0 :=
    mem_stabilizer_iff.mp (c.scalarSubgroup_le_stabilizer (hZ hz))
  have hg0 : c.scalar a • (g • (0 : F)) = g • (0 : F) := by
    rw [ha]
    simp only [mul_smul, inv_smul_smul, hz0]
  exact (c.scalar_fixed_iff a ha1 _).mp hg0

/-- In the actual semilinear zero stabilizer, a coefficient subgroup's
normalizer centralizes that subgroup. Uniqueness of KΓ coordinates and
cyclicity of Γ eliminate the conjugation action. -/
theorem stabilizer_inf_normalizer_le_centralizer [Finite F]
    {P : Subgroup X} (hP : P ≤ twoPoint (X := X) (F := F)) :
    stabilizer X (0 : F) ⊓ Subgroup.normalizer (P : Set X) ≤
      Subgroup.centralizer (P : Set X) := by
  let : IsCyclic (twoPoint (X := X) (F := F)) := c.twoPoint_isCyclic
  intro g hg u hu
  let δ : twoPoint (X := X) (F := F) := ⟨u, hP hu⟩
  have hv : g * u * g⁻¹ ∈ twoPoint (X := X) (F := F) :=
    hP ((Subgroup.mem_normalizer_iff.mp hg.2 u).mp hu)
  let ν : twoPoint (X := X) (F := F) := ⟨g * u * g⁻¹, hv⟩
  obtain ⟨a, γ, hfac⟩ := c.exists_scalar_mul_twoPoint ⟨g, hg.1⟩
  have hvscalar : (ν : X) * c.scalar a =
      c.scalar (Units.map (c.fieldAut ν).toMonoidHom a) * (ν : X) := by
    have h := c.conj_scalar ν 1 (c.fieldAut ν) (by intro x; simp) a
    have h' := congrArg (fun x : X => x * (ν : X)) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'
  have hcoords : c.scalar a * ((γ * δ : twoPoint (X := X) (F := F)) : X) =
      c.scalar (Units.map (c.fieldAut ν).toMonoidHom a) *
        ((ν * γ : twoPoint (X := X) (F := F)) : X) := by
    change c.scalar a * ((γ : X) * u) =
      c.scalar (Units.map (c.fieldAut ν).toMonoidHom a) * ((ν : X) * (γ : X))
    calc
      _ = g * u := by rw [← mul_assoc, hfac]
      _ = (ν : X) * g := by dsimp [ν]; group
      _ = (ν : X) * (c.scalar a * (γ : X)) := by rw [hfac]
      _ = _ := by rw [← mul_assoc, hvscalar, mul_assoc]
  have hsecond : γ * δ = ν * γ :=
    congrArg Prod.snd (c.scalar_mul_twoPoint_injective
      (a₁ := (a, γ * δ))
      (a₂ := (Units.map (c.fieldAut ν).toMonoidHom a, ν * γ)) hcoords)
  have hδν : δ = ν := by
    apply mul_left_cancel (a := γ)
    simpa only [mul_comm ν γ] using hsecond
  have hconj : g * u * g⁻¹ = u := (congrArg Subtype.val hδν).symm
  have hcomm : g * u = u * g := by
    have h := congrArg (fun x : X => x * g) hconj
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  exact hcomm.symm

/-- The zero stabilizer is exactly the full scalar normalizer. -/
theorem scalarSubgroup_normalizer_eq_stabilizer [Finite F]
    (hF : 3 ≤ Nat.card F) :
    Subgroup.normalizer (c.scalarSubgroup : Set X) = stabilizer X (0 : F) :=
  le_antisymm (c.scalar_normalizer_le_stabilizer le_rfl (c.scalarSubgroup_ne_bot hF))
    c.stabilizer_le_scalar_normalizer

end MulAction.SemilinearPointStabilizer.Coordinates
