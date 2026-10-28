module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Sections
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Displacement from a moved component constituent

If I and its image under a quadratic actor are disjoint, the quotient map
I → W/C_W(A) is injective. Thus moving I costs at least dim I in fixed
codimension. Moreover A ∩ K* is trivial when K* acts faithfully on I:
an element of this intersection preserves both subspaces and fixes their
difference vectors, so the diagonal lemma makes it trivial on I.

The exported theorem applies to the literal H*-invariant subquotients
constructed in `Sections`. Choosing an irreducible K* constituent, proving
the disjointness alternative, and bounding the rank outside K* remain
separate obligations. These inequalities do not assume their conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), terminal
§13.6, printed p.935, with the diagonal argument used in B.7.2, p.119.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound

variable {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem moved_space_finrank (ρ : Representation (ZMod 2) X W) (I : Submodule (ZMod 2) W)
    (A : Subgroup X) (a : X) (ha : a ∈ A)
    (hdis : Disjoint I (I.map (ρ a))) :
    Module.finrank (ZMod 2) I ≤ fixedCodim ρ A := by
  let f : I →ₗ[ZMod 2] W ⧸ fixedSpace ρ A := (fixedSpace ρ A).mkQ.comp I.subtype
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  have hvfix : (v : W) ∈ fixedSpace ρ A := (Submodule.Quotient.mk_eq_zero _).mp hv
  have hva : ρ a v = v := hvfix ⟨a, ha⟩
  have hvmap : (v : W) ∈ I.map (ρ a) := ⟨v, v.property, hva⟩
  have hv0 : (v : W) = 0 := (disjoint_iff_inf_le.mp hdis) ⟨v.property, hvmap⟩
  exact Subtype.ext hv0

omit [FiniteDimensional (ZMod 2) W] in
private theorem moved_space_disjoint_actor (ρ : Representation (ZMod 2) X W) (L A : Subgroup X)
    (I : Submodule (ZMod 2) W) (hI : L ≤ subspaceStabilizer ρ I)
    (hf : Function.Injective (invariantSubspace ρ L I hI).toRepresentation)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (a : X) (ha : a ∈ A) (hdis : Disjoint I (I.map (ρ a))) :
    Disjoint A L := by
  let := hA.2
  apply disjoint_iff_inf_le.mpr
  rintro b ⟨hbA, hbL⟩
  have hba : b * a = a * b :=
    congrArg Subtype.val (mul_comm (⟨b, hbA⟩ : A) ⟨a, ha⟩)
  have hfix := fixes_sup_of_fixes_diagonal ρ I a b hdis
    (fun v hv => (hI hbL v).2 hv) (fun v hv => ?_) (fun v _ => hq b hbA a ha v)
  · have he : (invariantSubspace ρ L I hI).toRepresentation ⟨b, hbL⟩ =
        (invariantSubspace ρ L I hI).toRepresentation 1 := by
      rw [map_one]
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact hfix v (Submodule.mem_sup_left v.property)
    exact congrArg Subtype.val (hf he)
  · obtain ⟨w, hw, rfl⟩ := hv
    rw [← Module.End.mul_apply, ← map_mul, hba, map_mul, Module.End.mul_apply]
    exact ⟨ρ b w, (hI hbL w).2 hw, rfl⟩

open Section08

/-- A moved faithful component constituent forces the same small quadratic
actor to meet K* trivially, while its dimension is bounded by twice the
original actor rank. The group K* is the actual star image of H∞. -/
theorem moved_star_constituent_bounds
    {G : Type*} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (U : Subrepresentation (starRepresentation H V₃ V₁ hn hk))
    (N : Subrepresentation U.toRepresentation)
    (I : Submodule (ZMod 2) (U ⧸ N.toSubmodule))
    (hI : Source.starImage H (terminalResidual H) ≤
      subspaceStabilizer N.quotientRepresentation I)
    (hf : Function.Injective (invariantSubspace N.quotientRepresentation
      (Source.starImage H (terminalResidual H)) I hI).toRepresentation)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hq : IsQuadratic N.quotientRepresentation A)
    (hsmall : fixedCodim N.quotientRepresentation A ≤ 2 * rank A)
    (a : Source.Hstar H) (ha : a ∈ A)
    (hdis : Disjoint I (I.map (N.quotientRepresentation a))) :
    Disjoint A (Source.starImage H (terminalResidual H)) ∧
      Module.finrank (ZMod 2) I ≤ fixedCodim N.quotientRepresentation A ∧
      Module.finrank (ZMod 2) I ≤ 2 * rank A := by
  have hd := moved_space_finrank N.quotientRepresentation I A a ha hdis
  exact ⟨moved_space_disjoint_actor N.quotientRepresentation _ A I hI hf hA hq a ha hdis,
    hd, hd.trans hsmall⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound
