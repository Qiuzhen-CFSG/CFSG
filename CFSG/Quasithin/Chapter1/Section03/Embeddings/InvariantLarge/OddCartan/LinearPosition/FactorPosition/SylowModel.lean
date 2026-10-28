module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.ProjectiveSylow
public import Theory.SpecificGroups.LinearCoefficientEquiv

/-!
# Sylow models for an arbitrary PSL₃ witness

A field equivalence identifies the supplied field of prime order with ZMod q.
The actual SL₃-to-PSL₃ projection has odd scalar kernel, so it gives an
isomorphism between their Sylow two-subgroups. Thus the proved SL₃ Sylow
presentations and cyclic-center theorem apply to the actual supplied group.

This is the model interface needed both for the odd Cartan normalization
argument and for comparison of central involutions. No model is inferred
from its order, and no assertion is made here about an almost-simple overgroup.

Source: Aschbacher–Smith, A.3.21(b), printed p.55, as used in the proof of
1.3.4, printed pp.510–511. The projection argument extends ProjectiveSylow.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J] [Finite J]

/-- The actual projective Sylow is isomorphic to any SL₃ Sylow at the same prime. -/
theorem isPSL_sylow_equiv_SL3 {q : ℕ} [Fact q.Prime]
    (hmodel : ClassicalGroup.IsPSL J 3 q) (S : Sylow 2 J)
    (T : Sylow 2 SL(3, ZMod q)) : Nonempty (S ≃* T) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hF)
  let f : J ≃* PSL(3, ZMod q) := e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)
  let U := S.mapSurjective (f := f.toMonoidHom) f.surjective
  let eS : S ≃* U := f.subgroupMap (S : Subgroup J)
  let eT : T ≃* U := Sylow.equivOfSurjectiveCoprime (Matrix.PSL3.projection (ZMod q))
    (Matrix.PSL3.projection_surjective (ZMod q))
    (by rw [Matrix.PSL3.projection_ker]
        exact Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center (ZMod q))) T U
  exact ⟨eS.trans eT.symm⟩

/-- The semidihedral-or-wreathed presentation for the actual projective Sylow. -/
theorem isPSL_sylow_shape {q : ℕ} [Fact q.Prime]
    (hq : Odd q) (hmodel : ClassicalGroup.IsPSL J 3 q) (S : Sylow 2 J) :
    Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S := by
  let T : Sylow 2 SL(3, ZMod q) := Classical.choice inferInstance
  obtain ⟨e⟩ := isPSL_sylow_equiv_SL3 hmodel S T
  rcases CFSG.Quasithin.ChapterA.Section03.sl3_sylow_shape q hq T with h | ⟨n, h⟩
  · exact Or.inl (ABG.semidihedral_equiv e.symm h)
  · exact Or.inr ⟨n, ABG.wreathed_equiv e.symm h⟩

/-- The center of the actual projective Sylow is cyclic. -/
theorem isPSL_sylow_center_cyclic {q : ℕ} [Fact q.Prime]
    (hq : Odd q) (hmodel : ClassicalGroup.IsPSL J 3 q) (S : Sylow 2 J) :
    IsCyclic (center S) :=
  (ABG.rank_two_and_cyclic_center_of_sylow_shape (isPSL_sylow_shape hq hmodel S)).2.2

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
