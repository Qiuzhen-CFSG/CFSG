module

public import Theory.Mathieu.M22.Properties.Simplicity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

private def m22Stab2Complement : SubMulAction m22Stab2 (Fin 22) where
  carrier := {x | x ≠ 1 ∧ x ≠ 2}
  smul_mem' g x hx := by
    constructor
    · exact perm_apply_ne_of_ne_fixed (m22Stab2Perm g) hx.1 (m22Stab2_fix1 g)
    · exact perm_apply_ne_of_ne_fixed (m22Stab2Perm g) hx.2 (m22Stab2_fix2 g)

private theorem m22Stab2_orbit_three_card :
    Nat.card (MulAction.orbit m22Stab2 (3 : Fin 22)) = 20 := by
  let : Fintype (MulAction.orbit m22Stab2 (3 : Fin 22)) := Fintype.ofFinite _
  let : Fintype m22Stab3 := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    m22Stab2 (3 : Fin 22)
  have hNat :
      Nat.card (MulAction.orbit m22Stab2 (3 : Fin 22)) *
          Nat.card m22Stab3 = Nat.card m22Stab2 := by
    simpa only [Nat.card_eq_fintype_card] using h
  rw [m22Stab3_card, m22Stab2_card] at hNat
  omega

private theorem m22Stab2Complement_carrier :
    (m22Stab2Complement : Set (Fin 22)) = ({1, 2} : Set (Fin 22))ᶜ := by
  ext x
  change (x ≠ 1 ∧ x ≠ 2) ↔ x ∉ ({1, 2} : Set (Fin 22))
  simp

private theorem m22Stab2_orbit_three_eq_complement :
    MulAction.orbit m22Stab2 (3 : Fin 22) =
      (m22Stab2Complement : Set (Fin 22)) := by
  let : Fintype (MulAction.orbit m22Stab2 (3 : Fin 22)) := Fintype.ofFinite _
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · intro x hx
    rcases MulAction.mem_orbit_iff.mp hx with ⟨g, hg⟩
    change m22Stab2Perm g 3 = x at hg
    constructor
    · intro hx1
      exact (perm_apply_ne_of_ne_fixed (m22Stab2Perm g) (by decide +kernel)
        (m22Stab2_fix1 g)) (hg.trans hx1)
    · intro hx2
      exact (perm_apply_ne_of_ne_fixed (m22Stab2Perm g) (by decide +kernel)
        (m22Stab2_fix2 g)) (hg.trans hx2)
  · have horbit :
        (MulAction.orbit m22Stab2 (3 : Fin 22)).ncard = 20 := by
      rw [← Set.fintypeCard_eq_ncard, ← Nat.card_eq_fintype_card]
      exact m22Stab2_orbit_three_card
    have hcompl : (m22Stab2Complement : Set (Fin 22)).ncard = 20 := by
      rw [m22Stab2Complement_carrier, Set.ncard_compl]
      simp
    rw [hcompl, horbit]

private theorem m22Stab2Complement_isPretransitive :
    MulAction.IsPretransitive m22Stab2 m22Stab2Complement := by
  constructor
  intro x y
  have hxOrbit : x.1 ∈ MulAction.orbit m22Stab2 (3 : Fin 22) := by
    rw [m22Stab2_orbit_three_eq_complement]
    exact x.2
  have hyOrbit : y.1 ∈ MulAction.orbit m22Stab2 (3 : Fin 22) := by
    rw [m22Stab2_orbit_three_eq_complement]
    exact y.2
  rcases MulAction.mem_orbit_iff.mp hxOrbit with ⟨gx, hgx⟩
  rcases MulAction.mem_orbit_iff.mp hyOrbit with ⟨gy, hgy⟩
  refine ⟨gy * gx⁻¹, ?_⟩
  apply Subtype.ext
  change (gy * gx⁻¹ : m22Stab2) • x.1 = y.1
  rw [mul_smul, ← hgx, inv_smul_smul]
  exact hgy

private theorem m22PointStabilizer_isTwoPretransitive :
    MulAction.IsMultiplyPretransitive m22Stab1
      (SubMulAction.ofStabilizer M22 (1 : Fin 22)) 2 := by
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  have : MulAction.IsPretransitive m22Stab1
      (SubMulAction.ofStabilizer M22 (1 : Fin 22)) :=
    MulAction.is_one_pretransitive_iff.mp
      ((SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := M22) (α := Fin 22) (a := (1 : Fin 22)) (n := 1)).mp
        m22_isTwoPretransitive)
  have : MulAction.IsPretransitive m22Stab2 m22Stab2Complement :=
    m22Stab2Complement_isPretransitive
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  let x2 : SubMulAction.ofStabilizer M22 (1 : Fin 22) :=
    ⟨2, by change (2 : Fin 22) ≠ 1; decide +kernel⟩
  obtain ⟨gx, hgx⟩ := MulAction.exists_smul_eq m22Stab1 a x2
  obtain ⟨gc, hgc⟩ := MulAction.exists_smul_eq m22Stab1 c x2
  have hxb2 : (gx • b).1 ≠ (2 : Fin 22) := by
    intro h
    apply hab
    apply smul_left_cancel gx
    apply Subtype.ext
    rw [hgx]
    exact h.symm
  have hyd2 : (gc • d).1 ≠ (2 : Fin 22) := by
    intro h
    apply hcd
    apply smul_left_cancel gc
    apply Subtype.ext
    rw [hgc]
    exact h.symm
  let xb : m22Stab2Complement :=
    ⟨(gx • b).1, (gx • b).2, hxb2⟩
  let yd : m22Stab2Complement :=
    ⟨(gc • d).1, (gc • d).2, hyd2⟩
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq m22Stab2 xb yd
  refine ⟨gc⁻¹ * (h : m22Stab1) * gx, ?_, ?_⟩
  · calc
      (gc⁻¹ * (h : m22Stab1) * gx) • a =
          gc⁻¹ • ((h : m22Stab1) • (gx • a)) := by simp [mul_smul]
      _ = gc⁻¹ • ((h : m22Stab1) • x2) := by rw [hgx]
      _ = gc⁻¹ • x2 := by
        congr 1
        apply Subtype.ext
        exact m22Stab2_fix2 h
      _ = c := by rw [← hgc]; simp
  · have hhval := congrArg Subtype.val hh
    change (h : m22Stab2) • (gx • b).1 = (gc • d).1 at hhval
    have hh' :
        ((h : m22Stab1) • (gx • b) :
          SubMulAction.ofStabilizer M22 (1 : Fin 22)) = gc • d := by
      apply Subtype.ext
      exact hhval
    calc
      (gc⁻¹ * (h : m22Stab1) * gx) • b =
          gc⁻¹ • ((h : m22Stab1) • (gx • b)) := by simp [mul_smul]
      _ = gc⁻¹ • (gc • d) := by rw [hh']
      _ = d := by simp

/-- The natural degree-22 action of M22 is three-transitive. -/
public theorem m22_isThreePretransitive :
    MulAction.IsMultiplyPretransitive M22 (Fin 22) 3 := by
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := M22) (α := Fin 22) (a := (1 : Fin 22)) (n := 2)).2
  exact m22PointStabilizer_isTwoPretransitive

end Sporadic.Mathieu

