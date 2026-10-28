module

public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.SemidihedralAutomizer
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.QGroupCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.GL23
public import CFSG.Quasithin.ClassicalModels
public import ABG.ChapterII.Section3.SourceThreeSemidihedralModel
public import Mathlib.Algebra.Field.ULift

/-!
# Semidihedral recognition in even characteristic

The actual involution centralizer is an ABG Q-group with trivial odd core,
semidihedral Sylow subgroup, and characteristic subgroup O²(H) isomorphic
to SL₂(3). The proved characteristic-three Q-group model theorem constructs
its GL₂(3) equivalence. I.4.2 then identifies the ambient group with PSL₃(3)
or M₁₁. All source model premises are supplied by the preceding marked core,
fusion, and automorphism arguments; no split extension is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.3(2),
printed pp.416–417; ABG II.3 Proposition 3 for the actual local model.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterI.SmallSylow

universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem source_power_of_residual
    (hcore : pPrimeCore 2 G = ⊥)
    (e : pResidual 2 G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    ABG.HasSourceQCharacteristicPower G 3 := by
  let F := ULift.{u} (ZMod 3)
  let eF : ZMod 3 ≃+* F := ULift.ringEquiv.symm
  let q : G ≃* (G ⧸ pPrimeCore 2 G) :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot |>.symm
  refine ⟨F, inferInstance, inferInstance, ?_, ?_, (pResidual 2 G).map q.toMonoidHom,
    ABG.characteristic_map_equiv q _ inferInstance, ?_⟩
  · refine ⟨3, 1, Nat.prime_three, by decide, by decide, ?_⟩
    simp [F]
  · simp [F]
  · exact ⟨(q.subgroupMap _).symm.trans (e.trans (GorensteinWalter.sl2RingEquiv eF))⟩

end CFSG.Quasithin.ChapterI.SmallSylow

namespace CFSG.Quasithin.ChapterI.SmallSylow
variable {G : Type*} [Group G] [Finite G]

/-- An actual GL₂(3) involution centralizer, constructed from the original
source hypotheses and its characteristic SL₂(3) residual. -/
public theorem source_gl23_centralizer
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (hT : Stellmacher.IsSemidihedralGroup T) :
    ∃ z : G, orderOf z = 2 ∧ Nonempty (centralizer ({z} : Set G) ≃* ABG.GL2 3 1) := by
  obtain ⟨z, hz, hTH, _, _, _, ⟨eR⟩, hcore⟩ := source_automizer T hE hno hT
  have hQ := semidihedral_involutionCentralizer_isQGroup T hT hno z hz
  have hS : ABG.HasQuasiDihedralSylowTwoSubgroups (centralizer ({z} : Set G)) := by
    refine ⟨T.subtype hTH, ?_⟩
    exact ABG.semidihedral_equiv (subgroupOfEquivOfLe hTH).symm hT
  exact ⟨z, hz, ABG.qGroup_equiv_gl2_three_of_corefree_semidihedral hQ hcore hS
    (source_power_of_residual hcore eR)⟩

/-- I.4.3(2), with actual PSL₃(3) and M₁₁ carriers and the original hypotheses. -/
public theorem semidihedral_recognition
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (hE : IsEvenCharacteristic G) (T : Sylow 2 G)
    (hT : Stellmacher.IsSemidihedralGroup T) :
    ClassicalGroup.IsPSL G 3 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11) := by
  obtain ⟨z, hz, hC⟩ := source_gl23_centralizer T (hE T) hno hT
  have hf := (semidihedral_fusion T hT hno).1
  rcases lemma_I_4_2 z hz (fun u hu => isConj_iff.mp (hf u z hu hz)) hC with h | h
  · exact Or.inl ⟨GaloisField 3 1, inferInstance, inferInstance,
      by simpa using GaloisField.card 3 1 (by decide), h⟩
  · exact Or.inr h
end CFSG.Quasithin.ChapterI.SmallSylow
