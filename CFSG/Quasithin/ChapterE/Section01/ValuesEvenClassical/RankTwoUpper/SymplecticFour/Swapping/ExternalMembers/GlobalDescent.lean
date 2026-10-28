module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Alignment.BorelCocycle
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.GroupAction.InvolutionSylow

/-!
# Global graph-field cocycle descent

An inner twist of the graph-field involution is again an involution precisely
when its matrix is a cocycle. Choose a Sylow subgroup fixed by that twist and
conjugate it to the standard unipotent subgroup. The transformed cocycle then
normalizes the unipotent subgroup, hence belongs to its Borel. The explicit
Borel descent removes it, giving a coboundary in the original matrix group.

This closes the global descent premise of the external E-member construction
for Aschbacher–Smith E.1.14(1), printed p.214, using the concrete graph-field
representative from 16.1.4(7), printed p.1171 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms GraphFieldFixedResidual InvolutionNormalForms
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
open CentralizerGeometry.Alignment.BorelCocycle

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem graphField_cocycle_coboundary (m : ℕ) (hF : Nat.card F = 2 ^ (2*m+1))
    (g : Sp F) (hc : g * graphFieldAut m g = 1) :
    ∃ h : Sp F, g = h * (graphFieldAut m h)⁻¹ := by
  let s := graphFieldAut (F := F) m
  let a := MulAut.conj g * s
  have hs : s ^ 2 = 1 := graphFieldAut_sq m hF
  have haa : a ^ 2 = 1 := (inner_twist_square_eq_one_iff s hs g).mpr hc
  obtain ⟨S, hS⟩ := MulAut.exists_fixed_sylow_two a haa
  let U := unipotentSylow hF (by omega)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (Sp F) U S
  change MulAut.conj k • U = S at hk
  let b := k⁻¹ * g * s k
  have hb : MulAut.conj b * s = (MulAut.conj k)⁻¹ * a * MulAut.conj k := by
    ext x
    simp only [b, a, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hss : s • U = U := by
    apply Sylow.ext
    exact graphFieldAut_map_unipotent m
  have hbU : MulAut.conj b • U = U := by
    calc
      _ = (MulAut.conj b * s) • U := by rw [mul_smul, hss]
      _ = U := by rw [hb, mul_smul, mul_smul, hk, hS, ← hk, inv_smul_smul]
  have hbB : b ∈ borel := by
    rw [borel_eq_normalizer_unipotent, mem_normalizer_iff_map_conj_eq]
    exact congrArg Sylow.toSubgroup hbU
  have hbc : b * s b = 1 := by
    apply (inner_twist_square_eq_one_iff s hs b).mp
    rw [hb]
    calc
      _ = (MulAut.conj k)⁻¹ * a ^ 2 * MulAut.conj k := by simp only [pow_two]; group
      _ = 1 := by rw [haa]; group
  obtain ⟨d, _, hd⟩ := borel_cocycle_coboundary m hF b hbB hbc
  refine ⟨k*d, ?_⟩
  change b = d * (s d)⁻¹ at hd
  change g = k*d * (s (k*d))⁻¹
  rw [map_mul, mul_inv_rev]
  dsimp [b] at hd
  calc
    g = k * (k⁻¹ * g * s k) * (s k)⁻¹ := by group
    _ = k*d * (s d)⁻¹ * (s k)⁻¹ := by rw [hd]; group
    _ = _ := by group

/-- The literal descent premise at the odd field exponent. -/
theorem graph_power_cocycle_coboundary {f : ℕ} (hF : Nat.card F = 2^f)
    (hf : Odd f) (g : Sp F) (hc : g * (ExceptionalGraph.graphAut ^ f) g = 1) :
    ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ f) h)⁻¹ := by
  obtain ⟨m, rfl⟩ := hf
  exact graphField_cocycle_coboundary m hF g hc

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
