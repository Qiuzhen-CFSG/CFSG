module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootCoordinates
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms

/-!
# Opposite unipotent subgroups over prime fields

The upper unitriangular subgroup has order p³ and index prime to p in
PSL₃(F). It and its inverse-transpose image are therefore Sylow p-subgroups.
The scalar projection kernel has order gcd(3,p−1), prime to p; the coprime
quotient normalizer theorem transports the SL₃ Borel normalizer to PSL₃.
This argument includes p = 3 without division by the matrix trace.

Sylow conjugacy normalizes the image of the upper subgroup. Simultaneously
normalizing its opposite is a further geometric step, not asserted here.
The explicit coordinate reversal followed by inverse transpose is the
nontrivial Dynkin symmetry used after an opposite pair has been fixed.

Source: GLS3, §§2.3 and 2.7 and Theorem 2.5.12(a),
`refs/KGroup/GLS3/chapter2.tex`, especially lines 1111–1115.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable (F : Type*) [Field F] [Finite F]

/-- The upper unitriangular subgroup in the actual projective quotient. -/
abbrev upperUnipotent : Subgroup PSL(3,F) := unipotent F

/-- Its inverse-transpose image, the lower unitriangular subgroup. -/
def lowerUnipotent : Subgroup PSL(3,F) := (upperUnipotent F).map (graph F).toMonoidHom

/-- Setwise preservation of both specified opposite unipotent subgroups. -/
def PreservesUnipotentPair (α : MulAut PSL(3,F)) : Prop :=
  (upperUnipotent F).map α.toMonoidHom = upperUnipotent F ∧
    (lowerUnipotent F).map α.toMonoidHom = lowerUnipotent F

theorem prime_not_dvd_unipotent_index {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    ¬ p ∣ (upperUnipotent F).index := by
  have hn (n : ℕ) (hn : 0 < n) : ¬ p ∣ p ^ n - 1 := by
    have hpow : p ∣ p ^ n := dvd_pow_self p (by omega : n ≠ 0)
    have hpos : 1 ≤ p ^ n := Nat.one_le_pow n p hp.pos
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_sub_iff_right hpos hpow).mp hd
    exact hp.not_dvd_one h1
  intro hd
  have hm := dvd_mul_of_dvd_left hd (Nat.gcd 3 (Nat.card F - 1))
  rw [upperUnipotent, index_unipotent_mul_scalar F, hF] at hm
  exact hp.not_dvd_mul (hn 3 (by decide)) (hn 2 (by decide)) hm

theorem upperUnipotent_isPGroup {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    IsPGroup p (upperUnipotent F) := by
  let : Fact p.Prime := ⟨hp⟩
  apply IsPGroup.of_card (n := 3)
  rw [upperUnipotent, card_unipotent, hF]

noncomputable def upperSylow {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    Sylow p PSL(3,F) := by
  let : Fact p.Prime := ⟨hp⟩
  exact (upperUnipotent_isPGroup F hp hF).toSylow (prime_not_dvd_unipotent_index F hp hF)

@[simp] theorem upperSylow_coe {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    (upperSylow F hp hF : Subgroup PSL(3,F)) = upperUnipotent F := rfl

theorem prime_coprime_projection_kernel {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    Nat.Coprime p (Nat.card (projection F).ker) := by
  rw [card_projectionKernel F, hF]
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hd' : p ∣ p - 1 := hd.trans (Nat.gcd_dvd_right 3 (p - 1))
  exact hp.not_dvd_one ((Nat.dvd_sub_iff_right hp.pos (dvd_refl p)).mp hd')

theorem normalizer_upperUnipotent {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    Subgroup.normalizer (upperUnipotent F) = borel F := by
  let : Fact p.Prime := ⟨hp⟩
  have hU : IsPGroup p (unipotentSL F) := by
    apply IsPGroup.of_card (n := 3)
    rw [card_unipotentSL, hF]
  let : Fact (IsPGroup p (unipotentSL F)) := ⟨hU⟩
  change Subgroup.normalizer ((unipotentSL F).map (projection F) : Set PSL(3,F)) = _
  rw [Subgroup.normalizer_map_eq_of_coprime_kernel p _ _ (projection_surjective F)
    (prime_coprime_projection_kernel F hp hF), normalizer_unipotentSL F]
  rfl

theorem normalizer_lowerUnipotent {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    Subgroup.normalizer (lowerUnipotent F) = (borel F).map (graph F).toMonoidHom := by
  rw [lowerUnipotent, ← Subgroup.map_equiv_normalizer_eq,
    normalizer_upperUnipotent F hp hF]

noncomputable def lowerSylow {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    Sylow p PSL(3,F) := by
  let : Fact p.Prime := ⟨hp⟩
  exact (upperSylow F hp hF).mapSurjective (f := (graph F).toMonoidHom) (graph F).surjective

@[simp] theorem lowerSylow_coe {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    (lowerSylow F hp hF : Subgroup PSL(3,F)) = lowerUnipotent F := rfl

theorem exists_inner_preserves_upper {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (α : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F), (upperUnipotent F).map (MulAut.conj g * α).toMonoidHom =
      upperUnipotent F := by
  let : Fact p.Prime := ⟨hp⟩
  let U := upperSylow F hp hF
  let V := U.mapSurjective (f := α.toMonoidHom) α.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(3,F) V U
  refine ⟨g, ?_⟩
  have h := congrArg (fun S : Sylow p PSL(3,F) => (S : Subgroup PSL(3,F))) hg
  change ((upperUnipotent F).map α.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at h
  rw [Subgroup.map_map] at h
  have he : (MulAut.conj g).toMonoidHom.comp α.toMonoidHom =
      (MulAut.conj g * α).toMonoidHom := rfl
  rw [he] at h
  exact h

/-- The matrix interchanging the first and third coordinate vectors. -/
def reversalGL : GL (Fin 3) F where
  val := !![0,0,1; 0,1,0; 1,0,0]
  inv := !![0,0,1; 0,1,0; 1,0,0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- Coordinate reversal followed by inverse transpose, the A₂ diagram symmetry. -/
def oppositionGraph : MulAut PSL(3,F) := linearConj F (reversalGL F) * graph F

omit [Finite F] in
theorem oppositionGraph_mem_standard : oppositionGraph F ∈ standard F :=
  (standard F).mul_mem (linearConj_mem_standard F _) (graph_mem_standard F)

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
