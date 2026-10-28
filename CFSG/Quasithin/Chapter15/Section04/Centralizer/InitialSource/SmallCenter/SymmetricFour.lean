module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Transfer
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.DihedralRecognition
public import Theory.SpecificGroups.SymmetricFourSylow
public import CFSG.Quasithin.ClassificationModels

/-!
# The symmetric-four local endpoint of the small-center source argument

An actual S₄ overgroup of the given Sylow subgroup makes that same Sylow
D₈. Even characteristic identifies the central involution centralizer
with this Sylow. The proved cyclic-index-two transfer theorem gives one
involution class, and the full I.4.1 order-eight recognition gives exactly
PSL₃(2) or A₆. No fusion, centralizer, or recognition conclusion is input.

This discharges the I.4.1 and transfer steps at the end of 15.4.7; producing
the S₄ local from the earlier fixed-pair block remains a separate source step.
Source: Aschbacher--Smith 15.4.7, p.1158, and I.4.1(2), pp.415--416.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
universe u
variable {G : Type u} [Group G] [Finite G]

theorem dihedral_eight_models {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) (e : T ≃* DihedralGroup 4) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  let := hG.simple
  obtain ⟨R,hR,hidx,z,hz,hzc,hout⟩ :=
    ChapterI.SmallSylow.dihedral_rotation_data (m := 2) (by decide) e
  let : IsCyclic R := hR
  have hzG : orderOf (z : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hc := ChapterI.SmallSylow.centralizer_eq_sylow_of_rotation_data T hG.evenCharacteristic
    R hidx z hz hzc hout
  have hclass := T.involutions_conjugate_of_cyclic_index_two R hidx
    (FamilySource.Transfer.no_index_two_of_simple hG.nonabelian) z hz
  let d : DihedralInvolutionCentralizerHypotheses G 3 := {
    two_le := by decide
    z := z
    involution := ⟨fun he => by simp [he] at hzG,
      by simpa only [hzG] using pow_orderOf_eq_one (z : G)⟩
    involutions_conjugate := fun v hv => isConj_iff.mp (hclass v (orderOf_eq_prime hv.2 hv.1))
    centralizer_equiv := ⟨(MulEquiv.subgroupCongr hc).trans e⟩ }
  exact d.recognition_of_three

/-- The original overgroup and embedding are sufficient for the two exceptional
models; no separate assumption on the ambient Sylow type is needed. -/
theorem symmetric_four_overgroup_models {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (e : M ≃* Equiv.Perm (Fin 4)) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  let S := T.subtype hTM
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨f⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four Q
  let eT : T ≃* S := (subgroupOfEquivOfLe hTM).symm
  let eS : S ≃* Q := e.subgroupMap (S : Subgroup M)
  exact dihedral_eight_models hG T (eT.trans (eS.trans f))

/-- The recognized models inhabit the unchanged eight-model Theorem E target. -/
theorem theoremE_of_symmetric_four_overgroup
    {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (e : M ≃* Equiv.Perm (Fin 4)) : ClassificationModels.IsTheoremEModel G := by
  rcases symmetric_four_overgroup_models hG T M hTM e with hl | ha
  · exact .linear_binary ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,hl⟩
  · exact .alternating_six ha

end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
