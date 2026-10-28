module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.VectorStabilizers.Inner
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer

/-!
# The nonsingular outer extension in corrected H.9.1(4)

The actual stabilizer is Aut(PSL in one lower dimension), via conjugation on
the kernel group. Its two-residual is the published embedded inner residual,
and an outer involution exchanges the two marked components and complements
that residual. The imported Sylow theorem places such an involution in every
actual Sylow two-subgroup of the vector stabilizer.

This completes the outer branch for the explicit `CoordinateAction` contract.
The existence and transport of that coordinate action, the pure parabolic
branch, and the adapted-pair theorem have separate assembly owners.

Source: Aschbacher–Smith, H.9.1(4), printed pp.389–390. The corrected statement
chooses the stabilizer Sylow independently of the pure-vector marking in (3).
-/

public section
namespace CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers

/-- The nonsingular outer-group clauses, with the actual residual embedding,
complement, and action on the marked components. -/
theorem nonsingular_outer_stabilizer_structure {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Nonempty (fullStabilizer d (x,f) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2))) ∧
    (pResidual 2 (fullStabilizer d (x,f))).map (fullStabilizer d (x,f)).subtype =
      innerResidual d (x,f) ∧
    ∃ s : fullStabilizer d (x,f),
      s.val ∉ MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup n) ∧
      s ^ 2 = 1 ∧ (innerInFull d (x,f)).IsComplement' (Subgroup.zpowers s) ∧
      d.representation s.val (x,0) = (0,f) ∧
      d.representation s.val (0,f) = (x,0) := by
  refine ⟨⟨fullStabilizerEquivAutProjective hn d h⟩, ?_, ?_⟩
  · rw [fullStabilizer_embedded_twoResidual hn d h, innerResidual_eq_innerStabilizer hn d h]
  · obtain ⟨a,ha,hout,hsq⟩ := exists_outer_involution (by omega) d h
    let s : fullStabilizer d (x,f) := ⟨a,ha⟩
    have hs2 : s ^ 2 = 1 := Subtype.ext hsq
    exact ⟨s, hout, hs2, outer_isComplement hn d h s hout hs2,
      outer_swaps_components hn d s hout⟩

end CFSG.Quasithin.ChapterH.NaturalDual
