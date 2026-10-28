module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Inputs
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Comparison

/-!
# Interfaces for the ambient calculation in 16.3.12

The conjugation action below is the actual action of T on L, with kernel T_C.
The smaller group is T₀ = T_C T_L ⟨u⟩. The outstanding rank calculation must
place every maximum elementary subgroup of T in this group. The separate
dihedral calculation must construct the rotations and the internal product;
the displayed multiplication identity fixes all three inclusions.

`RankGeometry` and `Decomposition` are outputs to be constructed, not additional
standing hypotheses of 16.3.12. In particular neither is an assertion that the
source theorem has been proved. The final assembly must construct both from
`Prepared` and the local rank-five input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1181–1182 / PDF pp.1198–1199, Lemma 16.3.12.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup Stellmacher ChapterB
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The subgroup called T₀ in the proof, formed with the marked u. -/
noncomputable def smallGroup (d : Prepared T z t L) : Subgroup G :=
  commutingSylow T L ⊔ componentSylow T L ⊔ zpowers d.marked.u

/-- The intrinsic center of a subgroup, included in the ambient group. -/
def ambientCenter (D : Subgroup G) : Subgroup G := (center D).map D.subtype

/-- The genuine conjugation action on L. -/
def componentAction (d : Prepared T z t L) : ↥T →* MulAut L :=
  L.normalizerMonoidHom.comp (inclusion d.counterexample.sylow_le_normalizer)

/-- The faithful image of an ambient subgroup's intersection with T. -/
def actionImage (d : Prepared T z t L) (A : Subgroup G) : Subgroup (MulAut L) :=
  (A.subgroupOf (T : Subgroup G)).map (componentAction d)

/-- The kernel is exactly T_C, with relative rather than ambient normality. -/
theorem componentAction_ker (d : Prepared T z t L) :
    (componentAction d).ker = (commutingSylow T L).subgroupOf (T : Subgroup G) := by
  ext x
  change inclusion d.counterexample.sylow_le_normalizer x ∈ L.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  change (x : G) ∈ centralizer (L : Set G) ↔
    (x : G) ∈ (T : Subgroup G) ⊓ centralizer (L : Set G)
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

/-- The smaller group is an actual subgroup of the ambient Sylow subgroup. -/
theorem smallGroup_le (d : Prepared T z t L) : smallGroup d ≤ (T : Subgroup G) :=
  sup_le (sup_le inf_le_left inf_le_left) (zpowers_le.mpr d.u_mem)

/-- The marked involution commutes with t because it belongs to K ≤ C_G(t). -/
theorem u_commutes_t (d : Prepared T z t L) : Commute d.marked.u t :=
  mem_centralizer_singleton_iff.mp
    (d.marked.component.1 d.marked.u_mem_enlargement)

/-- Both candidates for w lie in T and centralize T_L. -/
theorem candidate_mem_and_centralizes (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    w ∈ (T : Subgroup G) ∧ w ∈ centralizer (componentSylow T L : Set G) := by
  have htC : t ∈ centralizer (componentSylow T L : Set G) :=
    centralizer_le (show componentSylow T L ≤ L from inf_le_right)
      d.counterexample.mem_commutingSylow.2
  rcases hw with rfl | rfl
  · exact ⟨d.u_mem, d.u_centralizes_componentSylow⟩
  · exact ⟨T.mul_mem d.counterexample.mem_commutingSylow.1 d.u_mem,
      (centralizer _).mul_mem htC d.u_centralizes_componentSylow⟩

/-- Both candidates have square one. Nontriviality is proved separately. -/
theorem candidate_sq (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) : w ^ 2 = 1 := by
  have hu : d.marked.u ^ 2 = 1 := d.marked.u_orderOf ▸ pow_orderOf_eq_one _
  rcases hw with rfl | rfl
  · exact hu
  · rw [(u_commutes_t d).symm.mul_pow, hu,
      ← d.counterexample.involution, pow_orderOf_eq_one, mul_one]

/-- The marked action on L is nontrivial: it does not commute with (2,3,4).
This uses the actual pointwise pair stabilizer in the supplied S₈ marking. -/
theorem u_not_mem_componentCentralizer (d : Prepared T z t L) :
    d.marked.u ∉ centralizer (L : Set G) := by
  let q : Equiv.Perm (Fin 8) := Equiv.swap 2 3 * Equiv.swap 3 4
  have hq : q ∈ markedA6 := by
    constructor
    · change q ∈ alternatingGroup (Fin 8)
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    · constructor
      · change q 0 = 0
        decide
      · change q 1 = 1
        decide
  rw [← d.marked.component_image] at hq
  obtain ⟨a, ha, hea⟩ := hq
  change d.marked.equiv a = q at hea
  intro hu
  have hc : a * d.marked.equiv.symm (Equiv.swap 0 1 * Equiv.swap 2 3) =
      d.marked.equiv.symm (Equiv.swap 0 1 * Equiv.swap 2 3) * a :=
    Subtype.ext (hu a ha)
  have hp := congrArg d.marked.equiv hc
  simp only [map_mul, MulEquiv.apply_symm_apply, hea] at hp
  exact (by decide : ¬ q * (Equiv.swap 0 1 * Equiv.swap 2 3) =
    (Equiv.swap 0 1 * Equiv.swap 2 3) * q) hp

/-- Both candidates are nonidentity involutions, including t*u. -/
theorem candidate_order (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) : orderOf w = 2 := by
  apply orderOf_eq_prime (candidate_sq d hw)
  rcases hw with rfl | rfl
  · intro he
    have horder := d.marked.u_orderOf
    rw [he, orderOf_one] at horder
    omega
  · intro h
    have hu : d.marked.u = t⁻¹ := eq_inv_of_mul_eq_one_right h
    exact u_not_mem_componentCentralizer d
      (hu ▸ (centralizer (L : Set G)).inv_mem d.counterexample.mem_commutingSylow.2)

/-- Selection of the candidate with the larger fixed subgroup is always possible. -/
theorem exists_maximizing_candidate (d : Prepared T z t L) (Y : Subgroup G) :
    ∃ w : G, (w = d.marked.u ∨ w = t * d.marked.u) ∧
      ∀ x : G, x = d.marked.u ∨ x = t * d.marked.u →
        Nat.card ↥(Y ⊓ involutionCentralizer x) ≤
          Nat.card ↥(Y ⊓ involutionCentralizer w) := by
  rcases le_total (Nat.card ↥(Y ⊓ involutionCentralizer d.marked.u))
      (Nat.card ↥(Y ⊓ involutionCentralizer (t * d.marked.u))) with h | h
  · refine ⟨t * d.marked.u, Or.inr rfl, ?_⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact h
    · exact le_rfl
  · refine ⟨d.marked.u, Or.inl rfl, ?_⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact le_rfl
    · exact h

/-- The local Sylow group is a two-group in the ambient group. -/
theorem localSylow_isPGroup (d : Prepared T z t L) : IsPGroup 2 (localSylow d.P) :=
  d.P.isPGroup'.map (involutionCentralizer t).subtype

variable [Finite G]

/-- The local rank-five hypothesis gives the lower bound without assuming P ≤ T. -/
theorem five_le_rank (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) : 5 ≤ twoRank (T : Subgroup G) := by
  obtain ⟨S, hPS⟩ := (localSylow_isPGroup d).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hle : twoRank (localSylow d.P) ≤ twoRank (S : Subgroup G) :=
    Nat.log_mono_right (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hPS).1
  have heq : twoRank (S : Subgroup G) = twoRank (T : Subgroup G) := by
    rw [← hg]
    exact ThompsonObstruction.twoRank_map_equiv (MulAut.conj g) (T : Subgroup G)
  rwa [hP, heq] at hle

/-- Placement of the maximum elementary family gives the actual Thompson equality.
Keeping this reduction here lets the action-case proof use it without importing
the module that will assemble the finished source theorem. -/
theorem maxJ_eq_smallGroup (d : Prepared T z t L)
    (h : ∀ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), A ≤ smallGroup d) :
    elementaryAbelianMaxJ (T : Subgroup G) = elementaryAbelianMaxJ (smallGroup d) := by
  have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ smallGroup d := sSup_le h
  have hr : twoRank (smallGroup d) = twoRank (T : Subgroup G) :=
    twoRank_eq_of_intermediate _ _ hJ (smallGroup_le d)
  exact le_antisymm
    ((elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hJ).2
      (by rw [maxOrder_eq_two_pow_rank, maxOrder_eq_two_pow_rank, hr]))
    (maxJ_le_of_rank_eq (smallGroup_le d) hr)

/-- The numerical and placement outputs of the first paragraph of the proof.
`action_rank` computes T/T_C via its actual faithful conjugation image. -/
structure RankGeometry (d : Prepared T z t L) : Prop where
  rank : twoRank (T : Subgroup G) = 5
  centralizer_rank : twoRank (commutingSylow T L) = 2
  action_rank : twoRank (componentAction d).range = 3
  maximal_le : ∀ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), A ≤ smallGroup d
  maximal_intersection : ∀ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
    Nat.card ↥(A ⊓ commutingSylow T L) = 4
  maximal_image : ∀ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
    Nat.card (actionImage d A) = 8
  component_dihedral : Nonempty (componentSylow T L ≃* DihedralGroup 4)
  component_center_central :
    (T : Subgroup G) ≤ centralizer (ambientCenter (componentSylow T L) : Set G)

/-- An explicit, compatible internal product and the two source alternatives.
The cyclic group Y is `zpowers y`; no unrelated family label is used. -/
structure Decomposition (d : Prepared T z t L) where
  y : G
  rotation_le : zpowers y ≤ commutingSylow T L
  rotation_characteristic : ((zpowers y).subgroupOf (commutingSylow T L)).Characteristic
  rotation_index : (zpowers y).relIndex (commutingSylow T L) = 2
  rotation_order : ∃ n : ℕ, 2 ≤ n ∧ orderOf y = 2 ^ n
  reflection_generation : zpowers y ⊔ zpowers t = commutingSylow T L
  reflection_action :
    ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (commutingSylow T L ≃* DihedralGroup (2 ^ n))) ∧
      t⁻¹ * y * t = y⁻¹) ∨
    ((∃ (n : ℕ) (hn : 4 ≤ n),
      Nonempty (commutingSylow T L ≃* Semidihedral.StandardModel n hn)) ∧
      t⁻¹ * y * t = y⁻¹ * z)
  w : G
  candidate : w = d.marked.u ∨ w = t * d.marked.u
  maximizing : ∀ x : G, x = d.marked.u ∨ x = t * d.marked.u →
    Nat.card ↥(zpowers y ⊓ involutionCentralizer x) ≤
      Nat.card ↥(zpowers y ⊓ involutionCentralizer w)
  involution : orderOf w = 2
  R : Subgroup G
  R_le : R ≤ commutingSylow T L
  dihedral : ∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* DihedralGroup (2 ^ n))
  center_eq : ambientCenter R = zpowers z
  alternative :
    (w ∈ centralizer (commutingSylow T L : Set G) ∧
      ((R = commutingSylow T L ∧ ∃ n : ℕ, 2 ≤ n ∧
        Nonempty (commutingSylow T L ≃* DihedralGroup (2 ^ n))) ∨
       (R = omegaOneAmbient (commutingSylow T L) ∧
        R.relIndex (commutingSylow T L) = 2 ∧ ∃ (n : ℕ) (hn : 4 ≤ n),
        Nonempty (commutingSylow T L ≃* Semidihedral.StandardModel n hn)))) ∨
    (4 < orderOf y ∧ w⁻¹ * y * w = y * z ∧ R = zpowers (y ^ 2) ⊔ zpowers t)
  product : (R × componentSylow T L × zpowers w) ≃*
    elementaryAbelianMaxJ (T : Subgroup G)
  product_apply : ∀ (a : R) (b : componentSylow T L) (c : zpowers w),
    (product (a, b, c) : G) = (a : G) * (b : G) * (c : G)

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
