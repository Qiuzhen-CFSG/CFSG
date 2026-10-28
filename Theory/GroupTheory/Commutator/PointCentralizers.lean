module
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupAction.CoprimeHall
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Fixed points detected by a central commutator layer

Let an odd actor D normalize a finite two-group Z, with [Z,U] in a
D-fixed subgroup Z₀. Suppose each element of U outside K fixes at most Z₀
in Z. If D moves Z, then C_U(D) lies in K: otherwise the three-subgroup
lemma makes D quadratic on Z, contradicting coprime commutator idempotence.

Coprime decomposition of a finite two-group U then gives
U K = [U,D] K as a subgroup join. The ambient group need not be finite.
The literal graph application is the nonbinary torus argument in DGS,
*Groups and Graphs* (1985), 9.8, printed p.146.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- If every core-escaping point fixes just a small central seed in Z,
an odd actor moving Z has no core-escaping fixed point. -/
theorem fixed_subgroup_le_of_point_centralizers
    (Z Z₀ U K D : Subgroup G) [Finite Z] [Finite D]
    (hp : IsPGroup 2 Z) (ho : Odd (Nat.card D))
    (hDZ : D ≤ normalizer (Z : Set G))
    (hZU : ⁅Z,U⁆ ≤ Z₀) (hZD : Z₀ ≤ centralizer (D : Set G))
    (hpoint : ∀ u ∈ U, u ∉ K → Z ⊓ centralizer ({u} : Set G) ≤ Z₀)
    (hmove : ¬ Z ≤ centralizer (D : Set G)) : U ⊓ centralizer (D : Set G) ≤ K := by
  intro u hu
  by_contra hnot
  have huD : zpowers u ≤ centralizer (D : Set G) := zpowers_le.mpr hu.2
  have hfixed : ⁅⁅Z,D⁆,zpowers u⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm D,commutator_eq_bot_iff_le_centralizer.mpr huD,commutator_bot_left]
    · rw [commutator_comm (zpowers u)]
      exact commutator_eq_bot_iff_le_centralizer.mpr
        (((commutator_mono le_rfl (zpowers_le.mpr hu.1)).trans hZU).trans hZD)
  have hsmall : ⁅Z,D⁆ ≤ Z₀ := by
    apply le_trans ?_ (hpoint u hu.1 hnot)
    apply le_inf (le_normalizer_iff_commutator_le_left.mp hDZ)
    intro z hz a ha
    have hau : a = u := ha
    subst a
    exact commutator_eq_bot_iff_le_centralizer.mp hfixed hz u (mem_zpowers u)
  have hquad : ⁅⁅Z,D⁆,D⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hsmall.trans hZD)
  have hidem := commutator_closure_coprime_idempotent Z (D : Set G)
    (by simpa using hDZ) (fun d hd => by
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      rw [hn]
      apply Nat.Coprime.pow_right
      apply Odd.coprime_two_right
      apply ho.of_dvd_nat
      simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard (⟨d,hd⟩ : D))
  simp only [closure_eq] at hidem
  exact hmove (commutator_eq_bot_iff_le_centralizer.mp (hidem.symm.trans hquad))

/-- A fixed-subgroup bound turns coprime decomposition into a product with
the same kernel, without assuming the ambient group finite. -/
theorem sup_eq_commutator_sup_of_fixed_le
    (U K D : Subgroup G) [Finite U] [Finite D]
    (hp : IsPGroup 2 U) (ho : Odd (Nat.card D))
    (hDU : D ≤ normalizer (U : Set G))
    (hfixed : U ⊓ centralizer (D : Set G) ≤ K) :
    U ⊔ K = ⁅U,D⁆ ⊔ K := by
  let : Normalizes D U := ⟨hDU⟩
  let : MulDistribMulAction D U := conjMulDistribMulActionOfLeNormalizer D U hDU
  let : Group.IsNilpotent U := hp.isNilpotent
  have hcop : Nat.Coprime (Nat.card D) (Nat.card U) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact ho.coprime_two_right.pow_right n
  have hh := congrArg (Subgroup.map U.subtype)
    (fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := U) (A := D) (inferInstance : Group.IsSolvable U) hcop)
  rw [map_sup,commutatorAction_subgroup_conj_map_eq_commutator U D hDU,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  apply le_antisymm ?_ (sup_le ((le_normalizer_iff_commutator_le_left.mp hDU).trans le_sup_left) le_sup_right)
  apply sup_le ?_ le_sup_right
  apply hh.ge.trans
  apply sup_le ?_ le_sup_left
  rintro z ⟨u,hu,rfl⟩
  apply mem_sup_right
  apply hfixed
  refine ⟨u.property,?_⟩
  intro d hd
  have he := congrArg Subtype.val (hu ⟨d,hd⟩)
  change d * (u : G) * d⁻¹ = u at he
  exact mul_inv_eq_iff_eq_mul.mp he
end Subgroup
