module

public import Theory.SpecificGroups.SymplecticSix.Simplicity
public import Theory.SpecificGroups.SymplecticSix.FieldTransport
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The rank-three symplectic section over even fields

The projective action has point-stabilizer orbit sizes
1, q + q² + q³ + q⁴, q⁵. The resulting block sizes prove primitivity.
Together with transvection perfectness and Iwasawa's criterion, this proves
quasisimplicity of the literal PSp₆ central quotient over every field of
order 2ᵃ, a > 0. The binary case uses the existing six-space proof.

This discharges the semisimplicity input in Aschbacher--Smith A.2.18,
printed p.40. The geometric counting argument adapts Gerald Höhn's ATLAS,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
`Atlas/LinearGroups/Symplectic/{PointCount,Primitivity,PerfectLarge,SimplicityHighRank}.lean`
and `Atlas/Algebra/GeometricSumBounds.lean`. Covered by the ATLAS Research and
Attribution License 1.0; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. Changes: specialize to six-space, reuse CFSG's
module-compatible projective geometry and binary simplicity theorem, and
retain the supplied finite field in the actual matrix quotient.
-/

public section
noncomputable section
namespace Theory.SpecificGroups.Symplectic
open Matrix.PSp4Three Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F]
open scoped commutatorElement

private theorem perfect_large (hq : 3 < Nat.card F) : Group.IsPerfect (Sp 3 F) := by
  classical
  let := Fintype.ofFinite F
  have hcard : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    have h := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using lt_of_le_of_lt h hq
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have hc₂ : c ^ 2 ≠ 1 := fun h => (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2
  apply perfect_of_transvections
  intro v a
  by_cases hv : v = 0
  · subst v; simp
  obtain ⟨g, _, hg⟩ := exists_generated_send hv (smul_ne_zero hc.1 hv)
  let b := a / (c ^ 2 - 1)
  have hb : (c ^ 2 - 1) * b = a := mul_div_cancel₀ a (sub_ne_zero.mpr hc₂)
  have he : ⁅g, transvection v b⁆ = transvection v a := by
    rw [commutatorElement_def, transvection_conjugate, hg, transvection_scale,
      transvection_inverse, ← transvection_add]
    congr 1
    calc
      c ^ 2 * b + -b = (c ^ 2 - 1) * b := by ring
      _ = a := hb
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)


private theorem card_points_six :
    Nat.card (Points 3 F) = 1 + Nat.card F + Nat.card F ^ 2 + Nat.card F ^ 3 + Nat.card F ^ 4 + Nat.card F ^ 5 := by
  have h := Projectivization.card_of_finrank F (Vector 3 F)
    (show Module.finrank F (Vector 3 F) = 6 by simp [Matrix.PSp4Three.Vector, Index])
  simpa [Finset.sum_range_succ] using h

private theorem card_perpendicular_points_six (p : Points 3 F) :
    Nat.card {q : Points 3 F // Orthogonal p q} = 1 + Nat.card F + Nat.card F ^ 2 + Nat.card F ^ 3 + Nat.card F ^ 4 := by
  rw [← Nat.card_congr (perpendicularPointsEquiv p)]
  have hd : Module.finrank F (form p.rep).ker = 5 := by
    obtain ⟨v, hv⟩ := Frame.exists_partner form form_nondegenerate p.rep_nonzero
    have hr : LinearMap.range (form p.rep) = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      intro a
      exact ⟨a • v, by simp [map_smul, hv]⟩
    have h := (form p.rep).finrank_range_add_finrank_ker
    rw [hr, finrank_top, Module.finrank_self] at h
    have hdim : Module.finrank F (Vector 3 F) = 6 := by simp [Matrix.PSp4Three.Vector, Index]
    omega
  simpa [Finset.sum_range_succ] using Projectivization.card_of_finrank F (form p.rep).ker hd

private theorem block_nondivisibility {q : ℕ} (hq : 2 ≤ q) :
    ¬ (1 + q + q ^ 2 + q ^ 3 + q ^ 4) ∣ (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) ∧
    ¬ (1 + q ^ 5) ∣ (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) := by
  have hq2 : 2 * q ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_right q hq
  have hq3 : 2 * q ^ 2 ≤ q ^ 3 := by
    calc
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq
      _ = q ^ 3 := by ring
  have hq4 : 2 * q ^ 3 ≤ q ^ 4 := by
    calc
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_right (q ^ 3) hq
      _ = q ^ 4 := by ring
  have hq5 : 2 * q ^ 4 ≤ q ^ 5 := by
    calc
      _ ≤ q * q ^ 4 := Nat.mul_le_mul_right (q ^ 4) hq
      _ = q ^ 5 := by ring
  have hlt : 1 + q + q ^ 2 + q ^ 3 + q ^ 4 < q ^ 5 := by omega
  constructor
  · intro hd
    have he : 1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 = q * (1 + q + q ^ 2 + q ^ 3 + q ^ 4) + 1 := by ring
    rw [he] at hd
    have h1 : 1 + q + q ^ 2 + q ^ 3 + q ^ 4 ∣ 1 :=
      (Nat.dvd_add_iff_right (dvd_mul_left (1 + q + q ^ 2 + q ^ 3 + q ^ 4) q)).mpr hd
    have := Nat.le_of_dvd (by decide : 0 < 1) h1
    omega
  · rintro ⟨k, hk⟩
    by_cases hle : k ≤ 1
    · have := Nat.mul_le_mul_left (1 + q ^ 5) hle
      nlinarith
    · have := Nat.mul_le_mul_left (1 + q ^ 5) (show 2 ≤ k by omega)
      nlinarith

/-- The faithful projective action of the actual central quotient is primitive
in dimension six over every finite field. -/
theorem six_projective_preprimitive :
    MulAction.IsPreprimitive (PSp 3 F) (Points 3 F) := by
  classical
  let p : Points 3 F := ePoint 0
  let q := Nat.card F
  have hcard : Nat.card (Points 3 F) = 1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 :=
    card_points_six
  have hperp : Nat.card {x : Points 3 F // Orthogonal p x} = 1 + q + q ^ 2 + q ^ 3 + q ^ 4 :=
    card_perpendicular_points_six p
  have hq : 2 ≤ q := Finite.one_lt_card
  have hnd := block_nondivisibility hq
  apply Blocks.primitive_of_rankThree_nondivisibility p (suborbitIndex p)
    (suborbitIndex_self p) (fun x y h => suborbitIndex_transitive (by decide) p x y h)
    ![1, q + q ^ 2 + q ^ 3 + q ^ 4, q ^ 5] rfl
  · intro i
    fin_cases i
    · exact card_suborbit_zero p
    · change Nat.card {x : Points 3 F // suborbitIndex p x = 1} = q + q ^ 2 + q ^ 3 + q ^ 4
      rw [card_suborbit_one, hperp]
      omega
    · change Nat.card {x : Points 3 F // suborbitIndex p x = 2} = q ^ 5
      rw [card_suborbit_two, hcard, hperp]
      omega
  · change Nat.card (Points 3 F) = 1 + (q + q ^ 2 + q ^ 3 + q ^ 4) + q ^ 5
    simpa only [Nat.add_assoc] using hcard
  · change ¬ (1 + (q + q ^ 2 + q ^ 3 + q ^ 4)) ∣ Nat.card (Points 3 F)
    simpa only [hcard, ← Nat.add_assoc] using hnd.1
  · change ¬ (1 + q ^ 5) ∣ Nat.card (Points 3 F)
    simpa only [hcard] using hnd.2

/-- Simplicity of the literal central quotient when the field has more than
three elements. The even binary case is covered separately below. -/
theorem six_projective_simple_large (hq : 3 < Nat.card F) :
    IsSimpleGroup (PSp 3 F) := by
  let := six_projective_preprimitive (F := F)
  let := projective_nontrivial (F := F) (n := 3) (by decide)
  let : Group.IsPerfect (Sp 3 F) := perfect_large hq
  let : Group.IsPerfect (PSp 3 F) := inferInstance
  exact iwasawa.isSimpleGroup (Group.IsPerfect.commutator_eq_top (G := PSp 3 F))
    inferInstance

/-- Quasisimplicity of the actual PSp₆(2ᵃ) section, with its arbitrary field witness. -/
theorem six_projective_quasisimple {a : ℕ} (ha : 0 < a)
    (hc : Nat.card F = 2 ^ a) : IsQuasisimple (PSp 3 F) := by
  by_cases h2 : Nat.card F = 2
  · let : Group.IsPerfect (Sp 3 (ZMod 2)) := SymplecticSix.perfect_binary
    let : IsSimpleGroup (PSp 3 (ZMod 2)) := SymplecticSix.isSimpleGroup_binary
    let : IsQuasisimple (PSp 3 (ZMod 2)) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq
          (Group.IsPerfect.center_quotient_center_eq_bot (Sp 3 (ZMod 2)))).trans
            QuotientGroup.quotientBot).isSimpleGroup }
    exact IsQuasisimple.of_mulEquiv (SymplecticSix.pspFieldEquivZModTwo F h2).symm
  · have ha2 : 2 ≤ a := by
      by_contra h
      have : a = 1 := by omega
      simp [this] at hc
      exact h2 hc
    have hlarge : 3 < Nat.card F := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) ha2
      norm_num at h
      omega
    let : Group.IsPerfect (Sp 3 F) := perfect_large hlarge
    let : IsSimpleGroup (PSp 3 F) := six_projective_simple_large hlarge
    exact { simple := ((QuotientGroup.quotientMulEquivOfEq
        (Group.IsPerfect.center_quotient_center_eq_bot (Sp 3 F))).trans
          QuotientGroup.quotientBot).isSimpleGroup }

end Theory.SpecificGroups.Symplectic
end
