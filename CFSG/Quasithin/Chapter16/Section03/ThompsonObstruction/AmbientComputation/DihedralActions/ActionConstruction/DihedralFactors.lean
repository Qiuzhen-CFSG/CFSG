module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionConstruction.Choice
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.SemidihedralOmega

/-!
# Dihedral factors from the chosen rotations

The standard factor is the whole commuting Sylow subgroup when that subgroup
is dihedral, and its first omega subgroup when it is semidihedral. In the latter
case the involution normal forms identify omega with `⟨y²,t⟩` and give relative
index two. Independently, whenever the rotation has order greater than four,
`⟨y²,t⟩` is dihedral of order at least eight in either reflection-action case.

The reflection inverts the even rotations. Presentation recognition constructs
actual model equivalences, and the half-turn identity places the original `z`
in each factor. Its centrality and the dihedral center count identify the
ambient center as `⟨z⟩`. No condition on the maximizing involution's action is
used in either construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.3.12,
printed pp.1181–1182 / PDF pp.1198–1199. The maximizing-action alternative and
Thompson-subgroup assembly remain with the consumers of these two helpers.
-/

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.ActionConstruction
open Subgroup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}
variable (d : Prepared T z t L) (a : RotationChoice d)

include d in
omit [Finite G] in
private theorem reflection_inv : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two, d.counterexample.involution] using pow_orderOf_eq_one t)

private theorem even_rotation_inverted : t * a.y ^ 2 * t⁻¹ = (a.y ^ 2)⁻¹ := by
  have hz : z ^ 2 = 1 := d.counterexample.localSetup.involution ▸ pow_orderOf_eq_one z
  have hyz : Commute a.y z := mem_centralizer_singleton_iff.mp
    (d.counterexample.localSetup.sylow_centralizes (a.rotation_le (mem_zpowers _)).1)
  have he : t * a.y ^ 2 * t⁻¹ = (t⁻¹ * a.y * t) ^ 2 := by
    rw [reflection_inv d]
    simpa only [reflection_inv d] using (conj_pow (a := t) (b := a.y) (i := 2)).symm
  rw [he]
  rcases a.reflection_action d with ⟨_, hi⟩ | ⟨_, hi⟩
  · rw [hi, inv_pow]
  · rw [hi, hyz.inv_left.mul_pow, hz, mul_one, inv_pow]

omit [Finite G] in
private theorem exponent_ge_three (hlarge : 4 < orderOf a.y) : 3 ≤ a.exponent := by
  by_contra h
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show a.exponent ≤ 2 by omega)
  rw [a.order] at hlarge
  norm_num at hp
  omega

omit [Finite G] in
private theorem even_rotation_order : orderOf (a.y ^ 2) = 2 ^ (a.exponent - 1) := by
  have hh : 2 ^ a.exponent = 2 ^ (a.exponent - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    have := a.exponent_ge
    omega
  rw [orderOf_pow_of_dvd (by decide) (by rw [a.order, hh]; exact dvd_mul_left _ _),
    a.order, hh, Nat.mul_div_cancel _ (by decide)]

omit [Finite G] in
private theorem even_rotation_le : zpowers (a.y ^ 2) ⊔ zpowers t ≤ commutingSylow T L :=
  sup_le ((zpowers_le.mpr (pow_mem (mem_zpowers _) _)).trans a.rotation_le)
    (zpowers_le.mpr d.counterexample.mem_commutingSylow)

/-- The even rotations and the source reflection form a dihedral factor with the original center. -/
public theorem even_rotation_factor (hlarge : 4 < orderOf a.y) :
    let R := zpowers (a.y ^ 2) ⊔ zpowers t
    R ≤ commutingSylow T L ∧
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* DihedralGroup (2 ^ n))) ∧
      ambientCenter R = zpowers z := by
  let R := zpowers (a.y ^ 2) ⊔ zpowers t
  have hn := exponent_ge_three d a hlarge
  have ht2 : t ^ 2 = 1 := d.counterexample.involution ▸ pow_orderOf_eq_one t
  have hout : t ∉ zpowers (a.y ^ 2) := fun h => a.reflection_outside d
    ((zpowers_le.mpr (pow_mem (mem_zpowers _) _)) h)
  obtain ⟨_, ⟨e⟩⟩ := DihedralGroup.sup_zpowers_equiv_of_inversion (by positivity)
    (a.y ^ 2) t (even_rotation_order d a) ht2 hout (even_rotation_inverted d a)
  refine ⟨even_rotation_le d a, ⟨a.exponent - 1, by omega, ⟨e⟩⟩, ?_⟩
  have hzR : z ∈ R := by
    rw [← a.halfTurn d]
    have hh : 2 ^ (a.exponent - 1) = 2 * 2 ^ (a.exponent - 2) := by
      rw [show a.exponent - 1 = (a.exponent - 2) + 1 by omega, pow_succ, Nat.mul_comm]
    rw [hh, pow_mul]
    exact mem_sup_left (pow_mem (mem_zpowers _) _)
  have hZ : zpowers z ≤ ambientCenter R := by
    apply zpowers_le.mpr
    refine ⟨⟨z, hzR⟩, mem_center_iff.mpr ?_, rfl⟩
    intro v
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (d.counterexample.localSetup.sylow_centralizes ((even_rotation_le d a) v.property).1))
  apply (eq_of_le_of_card_ge hZ ?_).symm
  rw [ambientCenter, card_map_of_injective R.subtype_injective,
    DihedralGroup.center_card_of_equiv (by omega) e, Nat.card_zpowers,
    d.counterexample.localSetup.involution]

omit [Finite G] in
private theorem commuting_card : Nat.card (commutingSylow T L) = 2 * 2 ^ a.exponent := by
  have h := ((zpowers a.y).subgroupOf (commutingSylow T L)).index_mul_card
  rw [show ((zpowers a.y).subgroupOf (commutingSylow T L)).index = 2 from a.index,
    Nat.card_congr (subgroupOfEquivOfLe a.rotation_le).toEquiv,
    Nat.card_zpowers, a.order] at h
  exact h.symm

include d a in
/-- Without any condition on the maximizing action, the standard factor is the
whole dihedral group or the index-two omega subgroup of the semidihedral group. -/
public theorem exists_standard_factor : ∃ R : Subgroup G,
    R ≤ commutingSylow T L ∧
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* DihedralGroup (2 ^ n))) ∧
    ambientCenter R = zpowers z ∧
    ((R = commutingSylow T L ∧ ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (commutingSylow T L ≃* DihedralGroup (2 ^ n))) ∨
     (R = omegaOneAmbient (commutingSylow T L) ∧
      R.relIndex (commutingSylow T L) = 2 ∧ ∃ (n : ℕ) (hn : 4 ≤ n),
      Nonempty (commutingSylow T L ≃* Semidihedral.StandardModel n hn))) := by
  rcases a.reflection_action d with ⟨hD, _⟩ | ⟨hS, hact⟩
  · exact ⟨commutingSylow T L, le_rfl, hD, a.center_eq d, Or.inl ⟨rfl, hD⟩⟩
  · have hlarge : 4 < orderOf a.y := by
      obtain ⟨n, hn, ⟨e⟩⟩ := hS
      have hc := Nat.card_congr e.toEquiv
      rw [commuting_card d a, Semidihedral.standardModel_card] at hc
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hn
      norm_num at hp
      rw [a.order]
      omega
    let R := zpowers (a.y ^ 2) ⊔ zpowers t
    obtain ⟨hRC, hD, hZ⟩ := even_rotation_factor d a hlarge
    have ht2 : t ^ 2 = 1 := d.counterexample.involution ▸ pow_orderOf_eq_one t
    have hconj : t * a.y * t⁻¹ = a.y ^ (2 ^ (a.exponent - 1) - 1) := by
      rw [reflection_inv d] at hact ⊢
      rw [hact]
      calc
        a.y⁻¹ * z = a.y⁻¹ * a.y ^ (2 ^ (a.exponent - 1)) :=
          congrArg (a.y⁻¹ * ·) (a.halfTurn d).symm
        _ = a.y ^ (2 ^ (a.exponent - 1) - 1) := by
          apply mul_left_cancel (a := a.y)
          rw [mul_inv_cancel_left, ← pow_succ',
            Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide : 0 < 2))]
    have hO : omegaOneAmbient (commutingSylow T L) = R := by
      rw [← a.generation]
      exact Semidihedral.omegaOneAmbient_sup_eq a.exponent_ge a.y t a.order ht2 hconj
    have hi : R.relIndex (commutingSylow T L) = 2 := by
      have hout : t ∉ zpowers (a.y ^ 2) := fun h => a.reflection_outside d
        ((zpowers_le.mpr (pow_mem (mem_zpowers _) _)) h)
      have hcard := (DihedralGroup.sup_zpowers_equiv_of_inversion (by positivity)
        (a.y ^ 2) t (even_rotation_order d a) ht2 hout (even_rotation_inverted d a)).1
      have hm := relIndex_mul_relIndex (⊥ : Subgroup G) R (commutingSylow T L) bot_le hRC
      rw [relIndex_bot_left, relIndex_bot_left, hcard, commuting_card d a] at hm
      have hn := exponent_ge_three d a hlarge
      have hh : 2 ^ a.exponent = 2 ^ (a.exponent - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hh] at hm
      have hp : 0 < 2 ^ (a.exponent - 1) := by positivity
      nlinarith
    exact ⟨R, hRC, hD, hZ, Or.inr ⟨hO.symm, hi, hS⟩⟩

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.ActionConstruction
