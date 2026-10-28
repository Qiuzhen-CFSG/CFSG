module

public import Theory.Mathieu.M12.Properties.Simplicity
public import Theory.Mathieu.M12.Properties.Transitivity
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

/-- The center of `M12` is a normal subgroup. -/
public theorem m12_center_normal : (Subgroup.center M12).Normal := inferInstance

/-- A central element of the faithful two-transitive degree-12 action is trivial. -/
private theorem m12_centralizer_trivial
    (g : M12)
    (hcomm : ∀ h : M12,
      (g.1 : Equiv.Perm (Fin 12)) * (h.1 : Equiv.Perm (Fin 12)) =
        (h.1 : Equiv.Perm (Fin 12)) * (g.1 : Equiv.Perm (Fin 12))) :
    g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_contra hx
  obtain ⟨z, hzx, hzgx⟩ :=
    Fin.exists_ne_and_ne_of_two_lt x ((g.1 : Equiv.Perm (Fin 12)) x) (by omega)
  let source : Fin 2 ↪ Fin 12 :=
    { toFun := fun i => if i = 0 then x else (g.1 : Equiv.Perm (Fin 12)) x
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (Ne.symm hx hij).elim
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (hx hij).elim
        · rfl }
  let target : Fin 2 ↪ Fin 12 :=
    { toFun := fun i => if i = 0 then x else z
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (hzx hij.symm).elim
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (hzx hij).elim
        · rfl }
  have h5 : MulAction.IsMultiplyPretransitive M12 (Fin 12) 5 := m12_isFivePretransitive
  have : MulAction.IsMultiplyPretransitive M12 (Fin 12) 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := M12) (α := Fin 12) (m := 2) (n := 5)
      (by omega) (by rw [Nat.card_fin]; norm_num)
  obtain ⟨k, hk⟩ :=
    (inferInstance : MulAction.IsMultiplyPretransitive M12 (Fin 12) 2).exists_smul_eq source target
  have hk0 : k • x = x := by
    have hi := congrArg (fun e : Fin 2 ↪ Fin 12 => e 0) hk
    change k • source 0 = target 0 at hi
    rw [show source 0 = x by rfl, show target 0 = x by rfl] at hi
    exact hi
  have hk1 : k • ((g.1 : Equiv.Perm (Fin 12)) x) = z := by
    have hi := congrArg (fun e : Fin 2 ↪ Fin 12 => e 1) hk
    change k • source 1 = target 1 at hi
    rw [show source 1 = (g.1 : Equiv.Perm (Fin 12)) x by rfl,
      show target 1 = z by rfl] at hi
    exact hi
  change (k.1 : Equiv.Perm (Fin 12)) x = x at hk0
  change (k.1 : Equiv.Perm (Fin 12)) ((g.1 : Equiv.Perm (Fin 12)) x) = z at hk1
  have hc := hcomm k
  have happly := congrArg (fun p : Equiv.Perm (Fin 12) => p x) hc
  simp only [Equiv.Perm.mul_apply] at happly
  rw [hk0, hk1] at happly
  exact hzgx happly.symm

/-- The center of the simple group `M12` is trivial. -/
public theorem m12_center_eq_bot : Subgroup.center M12 = ⊥ := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff] at hg
    apply m12_centralizer_trivial g
    intro h
    exact (congrArg Subtype.val (hg h)).symm
  · intro hg
    simp only [Subgroup.mem_center_iff]
    intro h
    rw [hg]
    simp

/-- Conjugation gives the inner-automorphism homomorphism of `M12`. -/
public noncomputable def m12InnerAut : M12 →* MulAut M12 := MulAut.conj

/-- The inner-automorphism homomorphism of `M12` is injective. -/
public theorem m12InnerAut_injective : Function.Injective m12InnerAut := by
  intro g h hgh
  have hcenter : h⁻¹ * g ∈ Subgroup.center M12 := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun e : MulAut M12 => e x) hgh
    change g * x * g⁻¹ = h * x * h⁻¹ at hx
    calc
      x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by simp [mul_assoc]
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = (h⁻¹ * g) * x := by simp [mul_assoc]
  have hbot : h⁻¹ * g = 1 := by
    rw [m12_center_eq_bot] at hcenter
    exact Subgroup.mem_bot.mp hcenter
  exact (inv_mul_eq_one.mp hbot).symm

/-- The range of `m12InnerAut` is the inner automorphism subgroup of `M12`. -/
public noncomputable def m12InnerAutRange : Subgroup (MulAut M12) :=
  MonoidHom.range m12InnerAut

/-- The inner automorphism subgroup has the same cardinality as `M12`. -/
public theorem m12InnerAutRange_card :
    Nat.card m12InnerAutRange = Nat.card M12 := by
  exact Nat.card_congr (MonoidHom.ofInjective m12InnerAut_injective).toEquiv.symm

end Sporadic.Mathieu
