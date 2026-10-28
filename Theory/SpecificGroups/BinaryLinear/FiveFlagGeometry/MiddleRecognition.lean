module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.SpecificGroups.BinaryLinear.FiveParabolicRadical
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Recognition of the middle binary five-space parabolics

A subgroup containing a Sylow two-subgroup of GL₅(2), with relative
Sylow index 63, is an actual two- or three-space stabilizer. The existing
Sylow-overgroup theorem gives a basis flag. Its diagonal two-core quotient
reduces recognition to the sixteen subsets of four cuts. Coordinates and
inverse transpose identify either middle stabilizer with the literal
SL₅(2) two-space parabolic, whose radical excludes normal eight-groups.

Source: Aschbacher--Smith, the embedding discussion in 12.5.3, printed
p.818, and the tensor obstruction in 12.5.8(1), printed p.820.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic SmallParabolicLevi SmallParabolicLevi.TwoNodes
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private def linearOrder (n : ℕ) : ℕ := ∏ j : Fin n, (2^n - 2^j.val)

private theorem coordinate_card {α : Type*} [Fintype α] :
    Nat.card (BinaryLinear.GL (α → ZMod 2)) =
      linearOrder (Nat.card α) := by
  rw [Nat.card_eq_fintype_card (α := α)]
  let e : (α → ZMod 2) ≃ₗ[ZMod 2] Space (Fintype.card α) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Fintype.equivFin α).symm
  rw [Nat.card_congr (linearGroupCongr e).toEquiv,
    ← Nat.card_congr (matrixEquivLinear _).toEquiv, Matrix.card_GL_field]
  simp [linearOrder]

private def blockCount (s : Finset (Fin 4)) (k : Fin 5) : ℕ :=
  (Finset.univ.filter fun i : Fin 5 => (s.filter fun j => j.val < i.val).card = k.val).card

private theorem blockCount_eq (s : Finset (Fin 4)) (k : Fin 5) :
    blockCount s k = Nat.card (Block (cutLabel (s : Set (Fin 4))) k) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold blockCount cutLabel
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [Fin.ext_iff]
  have he : s.filter (fun j => j.val < i.val) =
      Finset.univ.filter (fun j : Fin 4 => j ∈ (s : Set (Fin 4)) ∧ j.val < i.val) := by
    ext j
    simp
  rw [he]
  apply Iff.of_eq
  congr 3

private def leviOrder (s : Finset (Fin 4)) : ℕ :=
  ∏ k : Fin 5, linearOrder (blockCount s k)

open scoped Classical in
private theorem quotient_card (b : FiveBasis) (cuts : Set (Fin 4)) :
    Nat.card (flagStabilizer b cuts ⧸ pCore 2 (flagStabilizer b cuts)) =
      leviOrder cuts.toFinset := by
  classical
  rw [Nat.card_congr (flagDiagonalQuotientEquiv b cuts).toEquiv, Nat.card_pi]
  simp_rw [coordinate_card]
  simp_rw [leviOrder, blockCount_eq, Set.coe_toFinset]

private theorem cut_certificate : ∀ s : Finset (Fin 4),
    leviOrder s = 63 * 2 ^ (leviOrder s).factorization 2 → s = {1} ∨ s = {2} := by
  decide +kernel

/-- The literal Sylow index 63 recognizes a middle parabolic, including its basis. -/
theorem middle_flag_of_sylow_index (S : Sylow 2 (LinearGroup 5))
    (H : Subgroup (LinearGroup 5)) (hSH : (S : Subgroup _) ≤ H)
    (hi : (S : Subgroup _).relIndex H = 63) :
    ∃ b : FiveBasis, H = flagStabilizer b {1} ∨ H = flagStabilizer b {2} := by
  classical
  obtain ⟨b,cuts,rfl⟩ := isFlagParabolic_of_sylow_le S H hSH
  let P := flagStabilizer b cuts
  let R := S.subtype hSH
  let q := QuotientGroup.mk' (pCore 2 P)
  let U := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 P))
  have hui : U.index = 63 := by
    change ((R : Subgroup P).map q).index = _
    rw [index_map_eq _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal R)]
    exact hi
  have hc := (U : Subgroup (P ⧸ pCore 2 P)).index_mul_card
  rw [U.card_eq_multiplicity, hui] at hc
  change 63 * 2 ^ (Nat.card (P ⧸ pCore 2 P)).factorization 2 = Nat.card (P ⧸ pCore 2 P) at hc
  rw [quotient_card] at hc
  rcases cut_certificate cuts.toFinset hc.symm with he | he
  · refine ⟨b, Or.inl ?_⟩
    apply congrArg (flagStabilizer b)
    simpa only [Set.coe_toFinset, Finset.coe_singleton] using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) he
  · refine ⟨b, Or.inr ?_⟩
    apply congrArg (flagStabilizer b)
    simpa only [Set.coe_toFinset, Finset.coe_singleton] using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) he

private theorem plane_equiv (W : Submodule (ZMod 2) (Space 5))
    (hd : Module.finrank (ZMod 2) W = 2) :
    Nonempty (BinaryLinear.parabolic W ≃* Representation.SL5ExteriorSquare.parabolic 2) := by
  let U := Representation.SL5ExteriorSquare.naturalFlag 2
  have hu : Module.finrank (ZMod 2) U = 2 :=
    Representation.SL5ExteriorSquare.finrank_naturalFlag 2 (by decide)
  obtain ⟨g,hg⟩ := FourParabolicAction.exists_linearEquiv_map_eq W U (hd.trans hu.symm)
  let e := ((MulAut.conj g).subgroupMap (BinaryLinear.parabolic W)).trans
    (MulEquiv.subgroupCongr ((InvariantNodeActions.inner_map_parabolic W g).trans
      (congrArg BinaryLinear.parabolic hg)))
  exact ⟨e.trans (Representation.SL5ExteriorSquare.parabolicLinearEquiv 2).symm⟩

/-- Both middle stabilizers have an actual isomorphism with the original matrix parabolic. -/
theorem middle_flag_equiv (b : FiveBasis) (i : Fin 4) (hi : i = 1 ∨ i = 2) :
    Nonempty (flagStabilizer b {i} ≃* Representation.SL5ExteriorSquare.parabolic 2) := by
  rw [flagStabilizer_singleton]
  rcases hi with rfl | rfl
  · exact plane_equiv _ (InvariantNodeActions.cutSpace_finrank b 1)
  · let W := flagSpace b 2
    let e := ((graphLinear 5).subgroupMap (BinaryLinear.parabolic W)).trans
      (MulEquiv.subgroupCongr (InvariantNodeActions.graph_map_parabolic W))
    have hd : Module.finrank (ZMod 2) (InvariantNodeActions.flagOrthogonal W) = 2 := by
      rw [InvariantNodeActions.flagOrthogonal_finrank,
        show Module.finrank (ZMod 2) W = 3 from InvariantNodeActions.cutSpace_finrank b 2]
    exact ⟨e.trans (plane_equiv _ hd).some⟩

/-- A full-Sylow subgroup of index 63 has no normal subgroup of order eight. -/
theorem no_normal_eight_of_sylow_index (S : Sylow 2 (LinearGroup 5))
    (H : Subgroup (LinearGroup 5)) (hSH : (S : Subgroup _) ≤ H)
    (hi : (S : Subgroup _).relIndex H = 63)
    (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N) : Nat.card N ≠ 8 := by
  obtain ⟨b,he | he⟩ := middle_flag_of_sylow_index S H hSH hi
  all_goals
    let e := (MulEquiv.subgroupCongr he).trans
      (middle_flag_equiv b _ (by first | exact Or.inl rfl | exact Or.inr rfl)).some
    let B := N.map e.toMonoidHom
    let : B.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    have hc := FiveParabolicRadical.matrix_no_normal_eight B (hN.map e.toMonoidHom)
    rwa [card_map_of_injective e.injective] at hc
end BinaryLinear.FiveFlagGeometry
