module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Models
public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.SpecificGroups.SU3.FiveCentralizerRadical.Outer
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Cyclic Sylow two-subgroups of the actual circle outer group

Linear and Suzuki outer groups are cyclic. In the unitary case the diagonal
outer kernel has exponent three and the field quotient is cyclic; a two-group
therefore embeds in that cyclic quotient. The perfect central-cover action
embeds the outer group of the original circle in the outer group of its simple
central quotient. This discharges the model hypothesis in Corollary 16.6(e).

Source: GLS IV, Chapter 2, Corollary 16.6(e), using Chapter 4, Lemma 3.1(a).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- A two-group faithfully represented in the actual simple-model outer
group is cyclic, with all automorphism coverage discharged. -/
public theorem simpleBender_outer_twoGroup_cyclic
    (hG : IsSimpleBenderGroup G) {D : Type*} [Group D]
    (hD : IsPGroup 2 D) (f : D →* MulAut.Outer G) (hf : Function.Injective f) :
    IsCyclic D := by
  obtain ⟨n,hn,hm⟩ := hG.exists_exponent
  rcases hm with hl | hs | hu
  · obtain ⟨e⟩ := hl
    let : IsCyclic (MulAut.Outer (PSL2BinaryMatrixGroup n)) :=
      Theory.PSL2.OuterSolvable.outer_isCyclic_of_field_coverage Linear.semilinear_coverage
    exact isCyclic_of_injective ((MulAut.outerCongr e).toMonoidHom.comp f)
      ((MulAut.outerCongr e).injective.comp hf)
  · obtain ⟨m,hnm,⟨e⟩⟩ := hs
    let : IsCyclic (MulAut.Outer (SuzukiMatrixGroup m)) := suzuki_outer_isCyclic m (by omega)
    exact isCyclic_of_injective ((MulAut.outerCongr e).toMonoidHom.comp f)
      ((MulAut.outerCongr e).injective.comp hf)
  · obtain ⟨E,hE,hEf,J,hJ,hcard,hfixed,⟨e⟩⟩ := hu
    let : Field E := hE
    let : Finite E := hEf
    let : IsSimpleGroup G := hG.isSimple
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.isSimpleGroup_congr.mp inferInstance
    exact HermitianForm.FiveCentralizerRadical.isCyclic_of_outer_injective_of_coverage J hJ
      (HermitianForm.EvenSemilinear.semilinear_coverage J hJ hn hcard
        (External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed)) hD
      ((MulAut.outerCongr e).toMonoidHom.comp f) ((MulAut.outerCongr e).injective.comp hf)

/-- The source outer Sylow hypothesis for the original perfect circle,
including its possible central cover, follows from its actual recognition. -/
public theorem source16_circle_outer_sylow_cyclic
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {u : G} (hu : PFAppendixIII.IsInvolution u)
    (huM : u ∈ M) (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))))
    (S : Sylow 2 (MulAut.Outer (localCircle Z (centralizer ({u} : Set G))))) :
    IsCyclic S := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  obtain ⟨z,hz,hzM,hzu⟩ := exists_distinguished_commuting_in_M h.disconnected r hu huM
  obtain ⟨_,hperfect,hmodel,_⟩ := localCircle_nonsolvable_structure h r ha B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩ hns
  let : Group.IsPerfect C := ⟨hperfect⟩
  let f := (MulAut.centralQuotientOuter (MulEquiv.refl (C ⧸ center C))).comp
    (S : Subgroup (MulAut.Outer C)).subtype
  exact simpleBender_outer_twoGroup_cyclic hmodel S.isPGroup' f
    ((MulAut.centralQuotientOuter_injective _).comp (S : Subgroup (MulAut.Outer C)).subtype_injective)

end BenderSuzuki.ZD
