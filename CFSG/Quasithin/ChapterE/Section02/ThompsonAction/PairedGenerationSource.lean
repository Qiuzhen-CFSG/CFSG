module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedGenerationGeometry
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedSource
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallThompson

/-!
# Excluding the natural linear pair from generation-one source groups

The actual B.5.6 source factors are permuted by the ambient action, and B.6.9
supplies their exchange inside the original Sylow image. The natural quotient
then constructs genuine elementary lifts of both factor Sylows. The paired
E-generation obstruction excludes every field degree greater than one. In
degree one, the marked S₃ product and the solvable centralizer kernel make
the original group solvable. Thus a nonsolvable generation-one source group
can have only the marked symmetric-five pair.
Source: Aschbacher--Smith B.6.9--10, E.2.3 and 6.1.5, pp.115--117,216--217,666.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_linear_not_isEGenerated_one
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (hF : 1 < F.degree) (c : d.MarkedProduct (linearNatural F 2)) :
    ¬ IsEGenerated 1 G := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hff : IsFFModule α := (lemma_B_2_7_local U q hq hk T hUT (hk ▸ hJ)).1
  have hcY : pCore 2 Y = ⊥ := by
    have hle : (pCore 2 Y).map Y.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map Y.subtype⟩
    rw [hcore] at hle
    apply bot_unique
    intro x hx
    exact Subtype.ext (hle (mem_map_of_mem Y.subtype hx))
  let D := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let η : D × D →* H := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  have hfirst : ((⊤ : Subgroup D).prod ⊥).map η = d.first.map Y.subtype := by
    rw [show η = Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom from rfl,
      ←map_map,c.first_eq]
  have hsecond : ((⊥ : Subgroup D).prod ⊤).map η = d.second.map Y.subtype := by
    rw [show η = Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom from rfl,
      ←map_map,c.second_eq]
  have htransport (A B : Subgroup Y) (g : H)
      (he : A.map (MulAut.conjNormal g).toMonoidHom = B) :
      (A.map Y.subtype).map (MulAut.conj g).toMonoidHom = B.map Y.subtype := by
    have hh := congrArg (map Y.subtype) he
    have hc : Y.subtype.comp (MulAut.conjNormal g).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp Y.subtype := by ext; rfl
    rw [map_map,hc,←map_map] at hh
    exact hh
  have hperm (g : H) :
      ((((⊤ : Subgroup D).prod ⊥).map η).map (MulAut.conj g).toMonoidHom =
        ((⊤ : Subgroup D).prod ⊥).map η ∧
       (((⊥ : Subgroup D).prod ⊤).map η).map (MulAut.conj g).toMonoidHom =
        ((⊥ : Subgroup D).prod ⊤).map η) ∨
      ((((⊤ : Subgroup D).prod ⊥).map η).map (MulAut.conj g).toMonoidHom =
        ((⊥ : Subgroup D).prod ⊤).map η ∧
       (((⊥ : Subgroup D).prod ⊤).map η).map (MulAut.conj g).toMonoidHom =
        ((⊤ : Subgroup D).prod ⊥).map η) := by
    rw [hfirst,hsecond]
    rcases d.automorphism_permutation hcY (MulAut.conjNormal g) with h | h
    · exact Or.inl ⟨htransport _ _ _ h.1,htransport _ _ _ h.2⟩
    · exact Or.inr ⟨htransport _ _ _ h.1,htransport _ _ _ h.2⟩
  have hex : ∃ t ∈ (T : Subgroup G),
      ((((⊤ : Subgroup D).prod ⊥).map η).map (MulAut.conj (q t)).toMonoidHom =
        ((⊥ : Subgroup D).prod ⊤).map η) ∧
      ((((⊥ : Subgroup D).prod ⊤).map η).map (MulAut.conj (q t)).toMonoidHom =
        ((⊤ : Subgroup D).prod ⊥).map η) := by
    obtain ⟨t,ht₁,ht₂⟩ := source_offender_two_factor_exists_sylow_exchange α
      (T.mapSurjective hq) hp hff hcore d
    obtain ⟨g,hg,he⟩ := t.property
    refine ⟨g,hg,?_,?_⟩
    · rw [hfirst,hsecond,he]
      exact htransport _ _ _ ht₁
    · rw [hfirst,hsecond,he]
      exact htransport _ _ _ ht₂
  obtain ⟨P,Q,hPQ⟩ := PairGeneration.sylow_pair Y c.action.groupEquiv (T.mapSurjective hq)
  have hlift := PairGeneration.paired_elementary_lifts T U q hq hk hUT hJ Y
    c.action.groupEquiv c.quotientMap c.quotientMap_surjective
    (fun g v => c.quotientMap_action g v) le_rfl P Q hPQ hex
  have hker : (T : Subgroup G) ⊓ q.ker = pCore 2 G := by
    rw [hk]
    exact (reduced_centralizer_sylow T hP U hU hJ).1
  exact PairGeneration.not_generated_of_coordinates F hF q hq T hker hcore Y
    c.action.groupEquiv P Q hPQ hperm hlift

theorem source_pair_of_isEGenerated_one
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hgen : IsEGenerated 1 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype)) :
    Group.IsSolvable G ∨ Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := (lemma_B_2_7_local U q hq hk T
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) (hk ▸ hJ)).1
  obtain ⟨_,_,_,hmodel⟩ := source_offender_two_factor_shared_natural α
    (T.mapSurjective hq) hp hff hcore d
  rcases hmodel with ⟨F,⟨c⟩⟩ | hc
  · by_cases hd : F.degree = 1
    · let : Group.IsSolvable H :=
        source_pair_degree_one_solvable α (T.mapSurjective hq) hp hff hcore d F hd c
      have hker := (minimalParabolic_reduced_image T hP q hq hcore hn).1
      let := minimalParabolic_core_solvable T hP
      let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective
        (f := inclusion hker) (inclusion_injective hker)
      exact Or.inl (Group.isSolvable_of_ker_le_range q.ker.subtype q (by rw [range_subtype]))
    · have hF : 1 < F.degree := by have := F.degree_pos; omega
      exact (paired_linear_not_isEGenerated_one T hP U hU hJ q hq hk d F hF c hgen).elim
  · exact Or.inr hc

end CFSG.Quasithin.ChapterE.ThompsonAction
