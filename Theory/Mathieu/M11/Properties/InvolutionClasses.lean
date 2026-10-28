module

public import Mathlib.Algebra.Group.Fin.Basic
public import Theory.Mathieu.M11.Properties.Transitivity
public import Theory.Mathieu.M11.Properties.Simplicity
public import Theory.Mathieu.M11.Properties.Parity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

private theorem m11_involution_support_card_le_eight
    (g : M11) (hg : orderOf g = 2) :
    ((g : Equiv.Perm (Fin 11)).support.card ≤ 8) := by
  let σ : Equiv.Perm (Fin 11) := g
  change σ.support.card ≤ 8
  have hsqG : g ^ 2 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hsq : σ ^ 2 = 1 := by
    exact congrArg (fun x : M11 => (x : Equiv.Perm (Fin 11))) hsqG
  have hsupportLe : σ.support.card ≤ 11 := by
    simpa using σ.support.card_le_univ
  obtain ⟨k, hk⟩ := Equiv.Perm.two_dvd_card_support hsq
  have hfixed :
      Fintype.card (Function.fixedPoints σ) = 11 - σ.support.card := by
    rw [σ.card_fixedPoints, σ.sum_cycleType]
    rfl
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hsq
  rw [show Equiv.Perm.sign σ = 1 from m11_sign_eq_one g, hfixed] at hsign
  change (1 : ℤˣ) = (-1) ^ ((11 - (11 - σ.support.card)) / 2) at hsign
  have hexp : (11 - (11 - σ.support.card)) / 2 = k := by omega
  rw [hexp] at hsign
  by_contra hle
  have hk5 : k = 5 := by omega
  rw [hk5] at hsign
  have hval := congrArg (fun u : ℤˣ => (u : ℤ)) hsign
  change (1 : ℤ) = (-1) ^ 5 at hval
  norm_num at hval

private theorem m11_existsUnique_smul_eq
    (x y : Fin 4 ↪ Fin 11) : ∃! g : M11, g • x = y := by
  obtain ⟨a, ha⟩ := m11_fourPointOrbitMap_bijective.surjective x
  obtain ⟨b, hb⟩ := m11_fourPointOrbitMap_bijective.surjective y
  change a • m11FourPointBase = x at ha
  change b • m11FourPointBase = y at hb
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · rw [← ha]
    change ((b * a⁻¹) * a) • m11FourPointBase = y
    simpa [mul_assoc] using hb
  · intro g hg
    have hga : (g * a) • m11FourPointBase = b • m11FourPointBase := by
      calc
        (g * a) • m11FourPointBase = g • (a • m11FourPointBase) :=
          mul_smul g a m11FourPointBase
        _ = g • x := by rw [ha]
        _ = y := hg
        _ = b • m11FourPointBase := hb.symm
    have heq : g * a = b := m11_fourPointOrbitMap_bijective.injective hga
    calc
      g = (g * a) * a⁻¹ := by simp
      _ = b * a⁻¹ := by rw [heq]
private def m11InvolutionTarget : Fin 4 ↪ Fin 11 where
  toFun i := ![1, 2, 3, 10] i
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The first standard generator represents the involution class of M11. -/
public theorem m11GeneratorAInM11_order : orderOf m11GeneratorAInM11 = 2 := by
  rw [← Subgroup.orderOf_coe m11GeneratorAInM11]
  exact m11GeneratorA_order

/-- Every involution of M11 is conjugate inside M11 to the first standard generator. -/
public theorem m11_involution_isConj_generatorA
    (g : M11) (hg : orderOf g = 2) :
    IsConj g m11GeneratorAInM11 := by
  classical
  let σ : Equiv.Perm (Fin 11) := g
  have hsqG : g ^ 2 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hsq : σ ^ 2 = 1 := by
    exact congrArg (fun x : M11 => (x : Equiv.Perm (Fin 11))) hsqG
  have hsupportLe : σ.support.card ≤ 8 :=
    m11_involution_support_card_le_eight g hg
  have hfixedCard : 2 ≤ Fintype.card (Function.fixedPoints σ) := by
    rw [σ.card_fixedPoints, σ.sum_cycleType]
    change 2 ≤ 11 - σ.support.card
    omega
  let fixedEmb : Fin 2 ↪ Function.fixedPoints σ :=
    (Function.Embedding.nonempty_of_card_le
      (α := Fin 2) (β := Function.fixedPoints σ) hfixedCard).some
  let f0 : Fin 11 := (fixedEmb 0).1
  let f1 : Fin 11 := (fixedEmb 1).1
  have hf0 : σ f0 = f0 := (fixedEmb 0).2
  have hf1 : σ f1 = f1 := (fixedEmb 1).2
  have hf01 : f0 ≠ f1 := by
    intro h
    have heq : fixedEmb 0 = fixedEmb 1 := Subtype.ext h
    have := fixedEmb.injective heq
    norm_num at this
  have hσne : σ ≠ 1 := by
    intro hσ
    have hg1 : g = 1 := by
      apply Subtype.ext
      exact hσ
    subst g
    norm_num at hg
  have hsupportPos : 0 < σ.support.card := by
    by_contra hpos
    have hzero : σ.support.card = 0 := by omega
    have hempty : σ.support = ∅ := Finset.card_eq_zero.mp hzero
    exact hσne (Equiv.Perm.support_eq_empty_iff.mp hempty)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hsupportPos
  have haMove : σ a ≠ a := Equiv.Perm.mem_support.mp ha
  let b : Fin 11 := σ a
  have hab : a ≠ b := haMove.symm
  have hback : σ b = a := by
    have happly := congrArg (fun p : Equiv.Perm (Fin 11) => p a) hsq
    change σ (σ a) = a at happly
    exact happly
  have ha0 : a ≠ f0 := by
    intro h
    apply haMove
    rw [h, hf0]
  have ha1 : a ≠ f1 := by
    intro h
    apply haMove
    rw [h, hf1]
  have hb0 : b ≠ f0 := by
    intro h
    apply ha0
    calc
      a = σ b := hback.symm
      _ = σ f0 := congrArg σ h
      _ = f0 := hf0
  have hb1 : b ≠ f1 := by
    intro h
    apply ha1
    calc
      a = σ b := hback.symm
      _ = σ f1 := congrArg σ h
      _ = f1 := hf1
  let source : Fin 4 ↪ Fin 11 := {
    toFun i := ![f0, a, f1, b] i
    inj' := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    }
  obtain ⟨h, hh⟩ :=
    (m11_existsUnique_smul_eq source m11InvolutionTarget).exists
  apply isConj_iff.mpr
  refine ⟨h, ?_⟩
  have hh0 : h • f0 = 1 := by
    have hi := congrArg (fun e : Fin 4 ↪ Fin 11 => e 0) hh
    change h • source 0 = m11InvolutionTarget 0 at hi
    rw [show source 0 = f0 by rfl,
      show m11InvolutionTarget 0 = (1 : Fin 11) by rfl] at hi
    exact hi
  have hh1 : h • a = 2 := by
    have hi := congrArg (fun e : Fin 4 ↪ Fin 11 => e 1) hh
    change h • source 1 = m11InvolutionTarget 1 at hi
    rw [show source 1 = a by rfl,
      show m11InvolutionTarget 1 = (2 : Fin 11) by rfl] at hi
    exact hi
  have hh2 : h • f1 = 3 := by
    have hi := congrArg (fun e : Fin 4 ↪ Fin 11 => e 2) hh
    change h • source 2 = m11InvolutionTarget 2 at hi
    rw [show source 2 = f1 by rfl,
      show m11InvolutionTarget 2 = (3 : Fin 11) by rfl] at hi
    exact hi
  have hh3 : h • b = 10 := by
    have hi := congrArg (fun e : Fin 4 ↪ Fin 11 => e 3) hh
    change h • source 3 = m11InvolutionTarget 3 at hi
    rw [show source 3 = b by rfl,
      show m11InvolutionTarget 3 = (10 : Fin 11) by rfl] at hi
    exact hi
  have hgf0 : g • f0 = f0 := hf0
  have hgf1 : g • f1 = f1 := hf1
  have hga : g • a = b := rfl
  have hgb : g • b = a := hback
  have hA0 : m11GeneratorAInM11 • (1 : Fin 11) = 1 := by
    change m11GeneratorA 1 = 1
    simp [m11GeneratorA, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have hA1 : m11GeneratorAInM11 • (2 : Fin 11) = 10 := by
    change m11GeneratorA 2 = 10
    simp [m11GeneratorA, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have hA2 : m11GeneratorAInM11 • (3 : Fin 11) = 3 := by
    change m11GeneratorA 3 = 3
    simp [m11GeneratorA, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have hA3 : m11GeneratorAInM11 • (10 : Fin 11) = 2 := by
    change m11GeneratorA 10 = 2
    simp [m11GeneratorA, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have hconjAction :
      (h * g * h⁻¹) • m11InvolutionTarget =
        m11GeneratorAInM11 • m11InvolutionTarget := by
    ext i
    fin_cases i
    · simp [Function.Embedding.smul_apply, m11InvolutionTarget]
      apply congrArg Fin.val
      calc
        (h * g * h⁻¹) • (1 : Fin 11) = h • (g • (h⁻¹ • (1 : Fin 11))) := by
          simp [mul_smul]
        _ = h • (g • f0) := by rw [← hh0, inv_smul_smul]
        _ = h • f0 := by rw [hgf0]
        _ = 1 := hh0
        _ = m11GeneratorAInM11 • (1 : Fin 11) := hA0.symm
    · simp [Function.Embedding.smul_apply, m11InvolutionTarget]
      apply congrArg Fin.val
      calc
        (h * g * h⁻¹) • (2 : Fin 11) = h • (g • (h⁻¹ • (2 : Fin 11))) := by
          simp [mul_smul]
        _ = h • (g • a) := by rw [← hh1, inv_smul_smul]
        _ = h • b := by rw [hga]
        _ = 10 := hh3
        _ = m11GeneratorAInM11 • (2 : Fin 11) := hA1.symm
    · simp [Function.Embedding.smul_apply, m11InvolutionTarget]
      apply congrArg Fin.val
      calc
        (h * g * h⁻¹) • (3 : Fin 11) = h • (g • (h⁻¹ • (3 : Fin 11))) := by
          simp [mul_smul]
        _ = h • (g • f1) := by rw [← hh2, inv_smul_smul]
        _ = h • f1 := by rw [hgf1]
        _ = 3 := hh2
        _ = m11GeneratorAInM11 • (3 : Fin 11) := hA2.symm
    · simp [Function.Embedding.smul_apply, m11InvolutionTarget]
      apply congrArg Fin.val
      calc
        (h * g * h⁻¹) • (10 : Fin 11) = h • (g • (h⁻¹ • (10 : Fin 11))) := by
          simp [mul_smul]
        _ = h • (g • b) := by rw [← hh3, inv_smul_smul]
        _ = h • a := by rw [hgb]
        _ = 2 := hh1
        _ = m11GeneratorAInM11 • (10 : Fin 11) := hA3.symm
  have hunique :=
    m11_existsUnique_smul_eq m11InvolutionTarget
      (m11GeneratorAInM11 • m11InvolutionTarget)
  exact hunique.unique hconjAction rfl

/-- M11 has a single conjugacy class of involutions. -/
public theorem m11_involutions_isConj
    (g h : M11) (hg : orderOf g = 2) (hh : orderOf h = 2) :
    IsConj g h :=
  (m11_involution_isConj_generatorA g hg).trans
    (m11_involution_isConj_generatorA h hh).symm

end Sporadic.Mathieu
