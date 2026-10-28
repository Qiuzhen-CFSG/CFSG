module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Actors
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.InvolutionModel
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# The SL₂ residual in the literal PSL₃ graph extension

The ambient centralizer has two-group quotient by its intersection with the
marked inner subgroup, so these two groups have the same solvable residual.
The checked projective involution-centralizer theorem identifies that residual
with SL₂ over the original field, including the projective scalar kernel.
Passing to C_G(z)^∞T preserves the same embedded residual.

This is the concrete residual input for the outer four-group E-member in
`LocalMember`. Source: Aschbacher--Smith A.3.21(a), printed p.55, and E.1.2(E2),
E.1.14(7), printed pp.210 and 214.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The full ambient centralizer has the actual SL₂ residual. -/
public theorem centralizer_residual_equiv_sl2 {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (z : graphExtension F) (hzL : z ∈ innerPart F) (hz : orderOf z = 2) :
    Nonempty (solvableResidual (centralizer ({z} : Set (graphExtension F))) ≃* SL(2,F)) := by
  let : Fact p.Prime := ⟨hp⟩
  let L := innerPart F
  let C := centralizer ({z} : Set (graphExtension F))
  let f := (QuotientGroup.mk' L).comp C.subtype
  let N := f.ker
  have hN : IsPGroup 2 (C ⧸ N) :=
    ((innerPart_quotient F).to_subgroup f.range).of_equiv
      (QuotientGroup.quotientKerEquivRange f).symm
  let : Group.IsNilpotent (C ⧸ N) := hN.isNilpotent
  let w : L := ⟨z, hzL⟩
  let e : N ≃* centralizer ({w} : Set L) :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
      invFun := fun x => ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
        (QuotientGroup.eq_one_iff _).mpr x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hF)
  have hmodel : ClassicalGroup.IsPSL L 3 p :=
    ⟨ZMod p, inferInstance, inferInstance, by simp,
      ⟨(innerPartEquiv F).symm.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)⟩⟩
  obtain ⟨es⟩ := Chapter1.XiEmbedding.InvariantLarge.OddCartan.isPSL_involution_solvableResidual
    ho hl hmodel w ((orderOf_submonoid w).symm.trans hz)
  exact ⟨(solvableResidualEquivOfSolvableQuotient N).symm.trans
    (e.solvableResidualEquiv.trans (es.trans (Matrix.SpecialLinearGroup.ringEquiv eF.symm)))⟩

/-- The residual supplement retains that same SL₂, via its actual inclusion. -/
public theorem supplement_residual_equiv_sl2 {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (T : Sylow 2 (graphExtension F)) (z : graphExtension F)
    (hzL : z ∈ innerPart F) (hz : orderOf z = 2)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) :
    Nonempty (solvableResidual (innerCentralizerSupplement F T z) ≃* SL(2,F)) := by
  let C := centralizer ({z} : Set (graphExtension F))
  let K := innerCentralizerSupplement F T z
  let D := (solvableResidual C).map C.subtype
  let : Group.IsPerfect D := Group.IsPerfect.map C.subtype
  have hKC : K ≤ C := sup_le (map_subtype_le _) hTz
  have he : (solvableResidual K).map K.subtype = D :=
    le_antisymm (map_solvableResidual_mono hKC)
      (le_map_solvableResidual_of_isPerfect D K le_sup_left)
  let er : solvableResidual K ≃* solvableResidual C :=
    ((solvableResidual K).equivMapOfInjective K.subtype K.subtype_injective).trans
      ((MulEquiv.subgroupCongr he).trans
        ((solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm)
  obtain ⟨ec⟩ := centralizer_residual_equiv_sl2 F hp ho hl hF z hzL hz
  exact ⟨er.trans ec⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors
