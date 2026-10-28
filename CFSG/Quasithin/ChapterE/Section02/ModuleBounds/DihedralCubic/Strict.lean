module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.RankOne
/-!
# The strict dihedral cubic ratio

The fixed subgroup Z gives codimension at most rank(A/Z)+1. This is
strictly less than twice the actor rank unless that rank is one. In the
remaining case the rank-one core theorem makes P elementary, so B is
fixed by A and |V/B|=2 bounds the codimension by one. The same actual
actor therefore has ratio strictly below two in every case.

The proof retains the original conjugation representation, actor map and
kernel. It needs no TI condition or recognition input for this family.
Source: Aschbacher–Smith E.2.10, E.2.13 and the dihedral branch of E.2.15,
combined manuscript (1 March 2004), printed pp.222–228.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X D Q : Type*} [Group X] [Finite X] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

omit [Finite X] [Finite D] in
private lemma actor_fixed_bound_of_fixed_subgroup
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (F : Subgroup X) (hFV : F ≤ V) (hFC : F ≤ centralizer (A V M g : Set X))
    (n : ℕ) (hc : Nat.card V ≤ 2 ^ n * Nat.card F) :
    fixedCodim ρ f.range ≤ n := by
  let C := fixedSpace ρ f.range
  have hfix (z : F) : Additive.ofMul (e ⟨z, hFV z.property⟩) ∈ C := by
    intro d
    obtain ⟨a, heq⟩ := d.property
    change ρ (d : D) (Additive.ofMul (e ⟨z, hFV z.property⟩)) = _
    rw [← heq]
    apply Additive.toMul.injective
    apply e.symm.injective
    apply Subtype.ext
    rw [ha]
    simp only [toMul_ofMul, e.symm_apply_apply]
    rw [hFC z.property _ a.property, mul_inv_cancel_right]
  let j : F → C := fun z => ⟨Additive.ofMul (e ⟨z, hFV z.property⟩), hfix z⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : V => (z : X))
      (e.injective (congrArg (fun z : C => z.val.toMul) hxy))
  have hcard : Nat.card Q ≤ 2 ^ n * Nat.card C := by
    rw [← Nat.card_congr e.toEquiv]
    exact hc.trans (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective j hj))
  have hQ : Nat.card Q = 2 ^ Module.finrank (ZMod 2) (Additive Q) := by
    rw [Nat.card_congr (Additive.ofMul : Q ≃ Additive Q)]
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q))
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) C := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C))
  rw [hQ, hC, ← pow_add] at hcard
  have hdim := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  have he := fixedCodim_add_finrank ρ f.range
  change fixedCodim ρ f.range + Module.finrank (ZMod 2) C = _ at he
  omega

/-- The stronger dimension estimate behind the dihedral cubic bound. -/
theorem actor_fixed_bound_add_one (h : Hypotheses T V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (f : A V M g →* D) (hk : f.ker = (Z V g).subgroupOf (A V M g))
    (he : IsElementaryTwo f.range)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    fixedCodim ρ f.range ≤ rank f.range + 1 := by
  apply actor_fixed_bound_of_fixed_subgroup e ρ f ha (Z V g) inf_le_left
    ((h.core_geometry.2.2.trans inf_le_right).trans (center_le_centralizer _))
  have hcA : Nat.card (A V M g) = Nat.card (Z V g) * Nat.card f.range := by
    have hc := f.ker.card_mul_index
    rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe
      (h.Z_le_B_inf_A.trans inf_le_right)).toEquiv] at hc
    exact hc.symm
  rw [h.card_V_eq_twice_A hcard, hcA, he.card_eq_two_pow_rank, pow_succ]
  exact le_of_eq (by ring)

omit [Finite X] [Finite D] in
/-- If the actual core is elementary, its B factor is fixed by the actor,
so the original V/B of order two bounds the fixed codimension by one. -/
theorem actor_fixed_bound_one_of_P_elementary (h : Hypotheses T V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (hP : IsElementaryAbelian 2 (P V M g))
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) : fixedCodim ρ f.range ≤ 1 := by
  let := hP
  apply actor_fixed_bound_of_fixed_subgroup e ρ f ha (B V M) inf_le_right
  · intro b hb a ha
    exact (P V M g).le_centralizer (show b ∈ P V M g from
      (show B V M ≤ P V M g from le_sup_left) hb) a
      ((show A V M g ≤ P V M g from le_sup_right) ha)
  · rw [h.card_V_eq_twice_A hcard, A, card_map_of_injective (MulAut.conj g).injective]
    norm_num

/-- The dihedral source actor has ratio strictly below two. No TI assumption
is needed for this particular family. -/
theorem dihedral_cubic_actor_strict (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have hd : fixedCodim ρ f.range < 2 * rank f.range := by
    by_cases hr : rank f.range = 1
    · have hi : (Z V g).relIndex (A V M g) = 2 := by
        change ((Z V g).subgroupOf (A V M g)).index = 2
        rw [← hk, index_ker, he.card_eq_two_pow_rank, hr]
        norm_num
      have hb := h.actor_fixed_bound_one_of_P_elementary hcard
        (h.P_elementary_of_actor_index_two hi) e ρ f ha
      omega
    · have hb := h.actor_fixed_bound_add_one hcard e ρ f hk he ha
      have hp := he.rank_pos
      omega
  have hr : actionRatio ρ f.range < 2 := by
    have h0 : (rank f.range : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt he.rank_pos)
    rw [actionRatio, ENNReal.div_lt_iff (Or.inl h0) (Or.inl (by simp))]
    exact_mod_cast hd
  exact ⟨hk, he, hc, hd, hr,
    (iInf_le_of_le f.range (iInf_le_of_le ⟨he, hc⟩ le_rfl)).trans_lt hr⟩
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
