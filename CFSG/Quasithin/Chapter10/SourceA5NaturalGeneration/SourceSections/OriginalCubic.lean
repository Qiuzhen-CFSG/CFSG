module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.Field
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearCartan
/-!
# A cubic Cartan in the original natural-four component

The actual paired source has field order four. Its canonical first component
therefore contains a cubic normalizing the local Baumann subgroup. This
component generates the original local join with the Sylow subgroup, so the
original L is its Sylow conjugate. Conjugating the cubic and embedding the
local join in G gives an actual cubic in L normalizing the original Baumann
subgroup. No block hypothesis or vanishing fixed-center premise is used.

Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747, using E.2.3.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance originalSelectedCubicFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

set_option backward.isDefEq.respectTransparency false in
/-- The original component itself contains a cubic normalizing the common
Baumann subgroup, before either characteristic-pair block is constructed. -/
theorem source_original_cubic_of_hstar_natural_four
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = 3 ∧
      A ≤ normalizer (baumann (T : Subgroup G) : Set G) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set X) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D hH hZH
  obtain ⟨d,KF,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  have hfield := source_original_paired_field_card D e hn hJ d KF c hexchange
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun Z _ _ => ChapterA.Section02.theoremA_knownSimple (G := Z))
    (fun Z _ _ => ChapterA.Section02.theoremC_knownSimple (G := Z))
    D.simpleQTKE T D.maximal
  have hG := (D.local_internal_module hu).sqtk
  have hP := source_a5_minimal_parabolic D e hn
  have hkc : q.ker = pCore 2 X := hk.trans (source_a5_local_module_kernel_eq_twoCore D e hn)
  obtain ⟨K,hK,_,_,_,_,_,_,_,_,hgen,_,A,hAK,hA,hAB⟩ :=
    first_component_localClass_with_cubic h36 hG S hP U hU hJ q hq hk hkc
      (source_join_not_solvable D) (source_join_fitting D) d KF hfield c hexchange
  obtain ⟨s,hs⟩ := source_original_component_conjugate_of_generating_component D K hK hgen
  let a := (MulAut.conj (s : X)).toMonoidHom
  let A' := A.map a
  have hA'L : A' ≤ L.subgroupOf X := by
    rw [hs]
    exact map_mono hAK
  have hsB : (s : X) ∈ normalizer (baumann (S : Subgroup X) : Set X) :=
    normalizer_le_normalizer_baumann _ ((S : Subgroup X).le_normalizer s.property)
  have hA'B : A' ≤ normalizer (baumann (S : Subgroup X) : Set X) := by
    rintro _ ⟨x,hx,rfl⟩
    exact (normalizer (baumann (S : Subgroup X) : Set X)).mul_mem
      ((normalizer (baumann (S : Subgroup X) : Set X)).mul_mem hsB (hAB hx))
      ((normalizer (baumann (S : Subgroup X) : Set X)).inv_mem hsB)
  have hBm := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
  change (baumann (S : Subgroup X)).map X.subtype =
    baumann ((S : Subgroup X).map X.subtype) at hBm
  have hSm : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  rw [hSm] at hBm
  refine ⟨A'.map X.subtype,?_,?_,?_⟩
  · exact (map_mono hA'L).trans_eq
      (map_subgroupOf_eq_of_le ((le_componentOrbit L T).trans le_sup_left))
  · rw [card_map_of_injective X.subtype_injective,
      show A' = A.map a from rfl,card_map_of_injective (MulAut.conj (s : X)).injective,hA]
  · have hm := (map_mono (f := X.subtype) hA'B).trans
      ((baumann (S : Subgroup X)).le_normalizer_map X.subtype)
    rwa [hBm] at hm
end CFSG.Quasithin.Chapter10
