module
public import Glauberman.FixedNormalPairTripleLattice
public import Glauberman.PushingUpCenterCovering

/-!
# Full intersection lattice for the original Main Hypothesis

The original natural quotient supplies the full fixed index sixteen and
Sylow-center commutator covering. Combined with the numerical pair descent,
exact center cells, and shifted-center estimate, it forces index four at
depth 3v. Every adjacent join therefore reconstructs its predecessor down
to printed row 3v - 1.

All conclusions share the original twisted conjugacy and one elementary-row
parameter. Source: Niles, *Pushing-up in finite groups* (1979), Proposition
4.6(b),(d)–(g), printed pages 46–47. The elementwise covering assertions of
4.7 and the nilpotence-class argument in Section 5 are later results.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_full_intersection_lattice
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    ∃ g : H,
      (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H ∧
      ∃ v : ℕ, 0 < v ∧
        let φ := twistedConjugacy (S : Subgroup H) α g
        IsElementaryAbelian 2 ↥(intervalCell φ 1 v) ∧
        intervalCell φ 1 v ∈ thompsonAbelianSubgroups (S : Subgroup H) ∧
        intervalCell φ 1 v ∈ thompsonAbelianSubgroups
          ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) ∧
        (∀ a b : ℕ, 1 ≤ a + b → a + b < 3 * v →
          intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b) ∧
        centerIn (S : Subgroup H) = intervalCell φ v (v + 1) ∧
        centerIn ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) = intervalCell φ (v + 1) v ∧
        centerIn (pCore 2 H) = intervalCell φ v v ∧
        center H = intervalCell φ (v + 1) (v + 1) ∧
        ⁅intervalCell φ 0 (2 * v), intervalCell φ v v⁆ ≤ intervalCell φ v (2 * v) := by
  obtain ⟨q, hq, hk, _, _, _, E, hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  obtain ⟨g, hgen, hinter, hpair⟩ := original_numerical_pair_of_natural_quotient
    hF S α hu K e hno q hq hk E hE
  let P : IntersectionPair H :=
    ⟨S, (S : Subgroup H).map (MulAut.conj g).toMonoidHom,
      twistedConjugacy (S : Subgroup H) α g⟩
  have hp : NumericalPair P.left P.right P.equiv := hpair
  obtain ⟨v, hv, hEv, hSv, hTv, hj, hzS, hzT, hzQ, hcomm⟩ :=
    P.exists_double_lattice_center_commutator hp
  have hzcore : centerIn (pCore 2 H) = intervalCell P.equiv v v := by
    calc
      centerIn (pCore 2 H) = centerIn (P.left ⊓ P.right) := congrArg centerIn hinter.symm
      _ = _ := hzQ
  obtain ⟨hglobal, _⟩ := original_psl2_four_full_center_fixed_spaces hF S α hu K e hf hno
  have hω := (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2
  have hzH_le : center H ≤ P.left ⊓ P.right := by
    change _ ≤ (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom
    rw [hinter]
    exact (hglobal.ge.trans inf_le_left).trans
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1)
  have hzH : center H = intervalCell P.equiv (v + 1) (v + 1) := by
    rw [center_eq_inf_centers_of_generating hgen hzH_le, hzS, hzT, intervalCell_inf,
      max_eq_right (Nat.le_succ v), max_eq_left (Nat.le_succ v)]
  have hi16 := (original_omega_supplement_natural_data q hq hk E hE ⊤ (by simp)).1
  simp only [coe_top, centralizer_univ] at hi16
  rw [hglobal, hω, hzcore] at hi16
  have hidouble := hp.rectangleStepIndex_double_eq_four v hv hzS hzQ
  have hi4 : (centerIn P.left).relIndex (intervalCell P.equiv v v) = 4 := by
    rw [hzS, intervalCell_relIndex P.equiv v v v (v + 1) le_rfl (Nat.le_succ v) (by omega)]
    simpa only [show v + v = 2 * v by omega] using hidouble
  have hZS : centerIn P.left ≤ intervalCell P.equiv v v := by
    rw [hzS]
    exact intervalCell_antitone P.equiv le_rfl (Nat.le_succ v)
  have hZHS : center H ≤ centerIn P.left := by
    rw [hzH, hzS]
    exact intervalCell_antitone P.equiv (Nat.le_succ v) le_rfl
  have hm := relIndex_mul_relIndex (center H) (centerIn P.left)
    (intervalCell P.equiv v v) hZHS hZS
  rw [hi4, hi16] at hm
  have hi : (center H).relIndex (centerIn P.left) = 4 := by omega
  have hcover : ⁅centerIn (P.left ⊓ P.right), P.left⁆ ⊔ center H = centerIn P.left := by
    have hc := original_psl2_four_center_commutator_covering hF S α hu K e hf hno
    change ⁅centerIn ((S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom),
      (S : Subgroup H)⁆ ⊔ center H = centerIn (S : Subgroup H)
    rw [hinter]
    exact hc
  have hitriple := P.rectangleStepIndex_triple_eq_four v hv hp.normal_left hj hzS hzQ hzH hcomm hcover hi
  have hjfull : ∀ a b : ℕ, 1 ≤ a + b → a + b < 3 * v →
      intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
        intervalCell P.equiv a b := by
    intro a b hab hbound
    apply intervalCell_sup_of_stepIndex_lower P.equiv hab (show a + b + 1 ≤ 3 * v by omega)
    rw [P.rectangleStepIndex_eq_four 0 hp, hitriple]
  exact ⟨g, hgen, hinter, v, hv, hEv, hSv, hTv, hjfull, hzS, hzT, hzcore, hzH, hcomm⟩

end Glauberman
