module

public import Stellmacher.Recognition.FongWreathedFusionOrientationDefs
public import Stellmacher.Recognition.FongWreathedBaseNormalizer

/-!
# Choosing Fong's orientation from the base-normalizer alternatives

Two base fusions suffice for the four fields of `BaseOrientation`: invert
`F² ~ EX`, and use the reality of `XF²` to invert `XF² ~ EJ`. The alternative
pair `F² ~ EXJ`, `XF² ~ E` becomes this pair after replacing the actual
presentation by `s' = sJ`, `t' = tJ`, `z' = z`.

The central involution `J` makes the replacement an involutory change of
base generators. It preserves `u = st` and `X = s²`; generation follows
because `J = (s't')²` belongs to the new generated subgroup. This module
assembles a compatible presentation from either base-normalizer alternative.
For a finite simple ambient group, the actual base normalizer supplies these
alternatives, giving the unconditional existence of a compatible presentation.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)* (1967), printed p. 70, before equation (5).
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG.Wreathed
variable {S : Type*} [Group S] (P : Presentation S 2)

private theorem J_sq : J P ^ 2 = 1 := by
  simpa only [J_orderOf] using pow_orderOf_eq_one (J P)

private theorem commute_J (g : S) : Commute g (J P) :=
  Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ P.u_mem_center 2) g

private theorem twist_product : (P.s * J P) * (P.t * J P) = P.u := by
  calc
    _ = P.s * (J P * P.t) * J P := by group
    _ = (P.s * P.t) * (J P * J P) := by rw [(commute_J P P.t).eq.symm]; group
    _ = P.u := by rw [← pow_two, J_sq, mul_one]; rfl

private def twist : Presentation S 2 where
  height := P.height
  card := P.card
  s := P.s * J P
  t := P.t * J P
  z := P.z
  s_pow := by rw [(commute_J P P.s).mul_pow, P.s_pow,
    show (J P) ^ (2 ^ 2) = 1 from by rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, J_sq, one_pow], one_mul]
  t_pow := by rw [(commute_J P P.t).mul_pow, P.t_pow,
    show (J P) ^ (2 ^ 2) = 1 from by rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, J_sq, one_pow], one_mul]
  z_sq := P.z_sq
  conj_s := by
    calc
      _ = (P.z⁻¹ * P.s) * (J P * P.z) := by group
      _ = (P.z⁻¹ * P.s * P.z) * J P := by rw [(commute_J P P.z).eq.symm]; group
      _ = _ := by rw [P.conj_s]
  conj_t := by
    calc
      _ = (P.z⁻¹ * P.t) * (J P * P.z) := by group
      _ = (P.z⁻¹ * P.t * P.z) * J P := by rw [(commute_J P P.z).eq.symm]; group
      _ = _ := by rw [P.conj_t]
  commute := by
    rw [twist_product]
    calc
      P.u = P.t * P.s := P.commute
      _ = (P.t * P.s) * (J P * J P) := by rw [← pow_two, J_sq, mul_one]
      _ = P.t * (P.s * J P) * J P := by group
      _ = P.t * (J P * P.s) * J P := by rw [(commute_J P P.s).eq]
      _ = _ := by group
  generate := by
    let H := Subgroup.closure ({P.s * J P, P.t * J P, P.z} : Set S)
    have hs : P.s * J P ∈ H := Subgroup.subset_closure (by simp)
    have ht : P.t * J P ∈ H := Subgroup.subset_closure (by simp)
    have hz : P.z ∈ H := Subgroup.subset_closure (by simp)
    have hu : P.u ∈ H := twist_product P ▸ H.mul_mem hs ht
    have hj : J P ∈ H := H.pow_mem hu 2
    have hss : P.s ∈ H := by
      simpa only [mul_assoc, ← pow_two, J_sq, mul_one] using H.mul_mem hs hj
    have htt : P.t ∈ H := by
      simpa only [mul_assoc, ← pow_two, J_sq, mul_one] using H.mul_mem ht hj
    apply top_unique
    rw [← P.generate]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hss
    · exact htt
    · exact hz

private theorem twist_u : (twist P).u = P.u := twist_product P
private theorem twist_X : X (twist P) = X P := by
  change (P.s * J P) ^ 2 = P.s ^ 2
  rw [(commute_J P P.s).mul_pow, J_sq, mul_one]


private theorem EX_inv : (E P * X P)⁻¹ = E P := by
  apply inv_eq_of_mul_eq_one_right
  change (P.s * P.s ^ 2) * P.s = 1
  simpa only [← pow_succ, ← pow_succ'] using (show P.s ^ (2 + 1 + 1) = 1 from P.s_pow)

private theorem EJ_inv : (E P * J P)⁻¹ = E P * X P * J P := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (show J P * J P = 1 from by rw [← pow_two, J_sq])]
  have hs : (E P)⁻¹ = E P * X P := by
    simpa only [inv_inv] using (congrArg Inv.inv (EX_inv P)).symm
  rw [hs, (commute_J P (E P * X P)).eq]

variable {G : Type*} [Group G] (T : Sylow 2 G) (Q : Presentation T 2)

private theorem conj_inv {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨g, by simpa [mul_assoc] using congrArg Inv.inv hg⟩

private theorem orientation_of_two
    (h₁ : IsConj ((F Q ^ 2 : T) : G) ((E Q * X Q : T) : G))
    (h₂ : IsConj ((X Q * F Q ^ 2 : T) : G) ((E Q * J Q : T) : G)) :
    BaseOrientation T Q := by
  refine ⟨h₁, ?_, h₂, ?_⟩
  · simpa only [← Subgroup.coe_inv, EX_inv] using conj_inv h₁
  · have hr := (T : Subgroup G).subtype.map_isConj (isConj_XF_sq_inv T Q)
    have hi : IsConj (((X Q * F Q ^ 2)⁻¹ : T) : G) (((E Q * J Q)⁻¹ : T) : G) :=
      conj_inv h₂
    rw [EJ_inv] at hi
    exact hr.trans hi

private theorem twist_EX : E (twist P) * X (twist P) = E P * X P * J P := by
  rw [twist_X]
  change (P.s * J P) * X P = _
  rw [mul_assoc, (commute_J P (X P)).eq.symm, ← mul_assoc]
  rfl

private theorem twist_EJ : E (twist P) * J (twist P) = E P := by
  change (P.s * J P) * (twist P).u ^ 2 = P.s
  rw [twist_u]
  change (P.s * J P) * J P = P.s
  rw [mul_assoc, ← pow_two, J_sq, mul_one]

/-- The two possible base-normalizer actions give a compatible presentation.
The second case uses Fong's generator change `s ↦ sJ`, `t ↦ tJ`. -/
public theorem exists_baseOrientation_of_baseFusion
    (h :
      (IsConj ((F Q ^ 2 : T) : G) ((E Q * X Q : T) : G) ∧
        IsConj ((X Q * F Q ^ 2 : T) : G) ((E Q * J Q : T) : G)) ∨
      (IsConj ((F Q ^ 2 : T) : G) ((E Q * X Q * J Q : T) : G) ∧
        IsConj ((X Q * F Q ^ 2 : T) : G) ((E Q : T) : G))) :
    ∃ P : Presentation T 2, BaseOrientation T P := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨Q, orientation_of_two T Q h₁ h₂⟩
  · refine ⟨twist Q, orientation_of_two T (twist Q) ?_ ?_⟩
    · simpa only [F_sq, twist_u, twist_EX] using h₁
    · simpa only [F_sq, twist_u, twist_X, twist_EJ] using h₂

/-- A wreathed Sylow subgroup of order 32 in a finite simple group admits an
actual presentation with all four of Fong's compatible base fusions. -/
public theorem exists_baseOrientation [Finite G] [IsSimpleGroup G]
    (hT : ABG.IsWreathedOfHeight T 2) :
    ∃ P : Presentation T 2, BaseOrientation T P := by
  obtain ⟨P⟩ := nonempty_presentation hT
  exact exists_baseOrientation_of_baseFusion T P (baseFusion_alternatives T P)

end Stellmacher.Recognition.FongWreathedIntrinsic
