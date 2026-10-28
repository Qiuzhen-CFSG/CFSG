module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ParabolicAutomorphisms

/-!
# An outer-preserved binary five-space flag with a factor seven

A proper subgroup containing a full Sylow two-subgroup is a flag stabilizer.
An outer automorphism preserving it reverses the cut dimensions. The diagonal
quotient retains its factor seven because the kernel is a two-group. The four
possible reversal-invariant cut sets then leave precisely dimensions one and
four: the parabolic with middle-node Levi factor SL3(2).

The Chapter 12 nonsingular-point application supplies the full Sylow, factor
seven and actual outer normalizer through the same central-cover action.
Source: Aschbacher--Smith 12.1.1, printed p.789, and C.2.7, pp.145--147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace BinaryLinear.FiveFlagGeometry
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
open BinaryLinear.InvariantNodeActions
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

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


private theorem symmetric_cuts_certificate : ∀ s : Finset (Fin 4),
    s ≠ ∅ → (∀ i ∈ s, i.rev ∈ s) → 7 ∣ leviOrder s → s = {0,3} := by
  decide +kernel

private theorem preserved_cuts_reverse (b : FiveBasis) (cuts : Set (Fin 4))
    (a : MulAut (LinearGroup 5)) (ha : a ∉ MulAut.innerSubgroup (LinearGroup 5))
    (hp : (flagStabilizer b cuts).map a.toMonoidHom = flagStabilizer b cuts) :
    ∀ i ∈ cuts, i.rev ∈ cuts := by
  obtain ⟨g,rfl | rfl⟩ := inner_graph (Or.inr rfl) a
  · exact (ha ⟨g,rfl⟩).elim
  · intro i hi
    have hle : flagStabilizer b cuts ≤ parabolic (cutSpace b i) := by
      intro x hx
      exact (mem_cutStabilizer b cuts x).mp hx i hi
    have hm := map_mono (f := (graphLinear 5 * MulAut.conj g).toMonoidHom) hle
    rw [hp,graph_inner_map_parabolic] at hm
    let W := flagOrthogonal ((cutSpace b i).map g.toLinearMap)
    have hd : Module.finrank (ZMod 2) W = 4-i.val := graph_inner_cut_finrank b g i
    have h0 : W ≠ ⊥ := by
      intro he
      rw [he,finrank_bot] at hd
      have := i.isLt
      omega
    have h1 : W ≠ ⊤ := by
      intro he
      rw [he,finrank_top,Module.finrank_fin_fun] at hd
      omega
    obtain ⟨j,hj,he⟩ := (cutStabilizer_le_parabolic_iff b cuts W h0 h1).mp hm
    have hh := congrArg (fun U : Submodule (ZMod 2) (Space 5) => Module.finrank (ZMod 2) U) he
    rw [hd,cutSpace_finrank] at hh
    have hji : j = i.rev := by
      apply Fin.ext
      simp only [Fin.val_rev]
      have := i.isLt
      omega
    exact hji ▸ hj

/-- A proper Sylow overgroup with a factor seven and an outer normalizer
is the actual line-hyperplane flag stabilizer. -/
theorem outer_seven_middle_flag (P : Sylow 2 (LinearGroup 5))
    (M : Subgroup (LinearGroup 5)) (hPM : (P : Subgroup _) ≤ M)
    (hne : M ≠ ⊤) (h7 : 7 ∣ Nat.card M)
    (a : MulAut (LinearGroup 5)) (ha : a ∉ MulAut.innerSubgroup (LinearGroup 5))
    (hm : M.map a.toMonoidHom = M) :
    ∃ b : FiveBasis, M = flagStabilizer b {0,3} := by
  classical
  obtain ⟨b,cuts,rfl⟩ := isFlagParabolic_of_sylow_le P M hPM
  have hr := preserved_cuts_reverse b cuts a ha hm
  have hc : 7 ∣ Nat.card (flagStabilizer b cuts ⧸ pCore 2 (flagStabilizer b cuts)) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := flagStabilizer b cuts)).exists_card_eq
    rw [←(pCore 2 (flagStabilizer b cuts)).card_mul_index,hk] at h7
    exact ((by decide : Nat.Coprime 7 2).pow_right k).dvd_of_dvd_mul_left h7
  rw [quotient_card] at hc
  have he := symmetric_cuts_certificate cuts.toFinset (by
    intro he
    have hz : cuts = ∅ := by simpa using congrArg (fun s : Finset (Fin 4) => (s : Set (Fin 4))) he
    exact hne (by rw [hz,flagStabilizer_empty]))
    (by simpa using hr) hc
  have hcuts : cuts = {0,3} := by
    simpa using congrArg (fun s : Finset (Fin 4) => (s : Set (Fin 4))) he
  exact ⟨b,by rw [hcuts]⟩
end BinaryLinear.FiveFlagGeometry
