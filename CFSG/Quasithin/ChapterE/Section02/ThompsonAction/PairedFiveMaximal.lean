module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.FactorMarking
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSaturation

/-!
# The actual maximal-overgroup intersections on both source S₅ factors

The original minimal parabolic descends through the genuine action quotient.
The same prescribed Sylow exchanger and actual Baumann image activate the
two component Borel calculations. Pulling the original unique maximal
overgroup through this quotient gives exactly the two marked S₄ intersections.
The image hypothesis is supplied by the proved paired Baumann theorem.

Source: Aschbacher--Smith C.1.24, E.2.3(3) and3.1.7.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation ChapterC.SymmetricFive
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem source_paired_maximal_images
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (a b : Sym)
    (hS : (baumann (T : Subgroup G)).map q =
      (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
          ((offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype.comp
            c.action.groupEquiv.symm.toMonoidHom)) :
    ((minimalParabolicMax T hP).map q).comap
      (Paired.leftFactorMap (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))
        c.action.groupEquiv) = pointFour.map (MulAut.conj a).toMonoidHom ∧
    ((minimalParabolicMax T hP).map q).comap
      (Paired.rightFactorMap (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))
        c.action.groupEquiv) = pointFour.map (MulAut.conj b).toMonoidHom := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  let e := c.action.groupEquiv
  let R := T.mapSurjective hq
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp : IsMinimalParabolicOver R ⊤ := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hmax : minimalParabolicMax T hP = (minimalParabolicMax R hp).comap q := by
    apply (minimalParabolicMax_unique T hP _ _).symm
    · exact isCoatom_comap_of_surjective hq (minimalParabolicMax_spec R hp).1
    · exact map_le_iff_le_comap.mp (minimalParabolicMax_spec R hp).2
  have hmaxmap : (minimalParabolicMax T hP).map q = minimalParabolicMax R hp := by
    rw [hmax,map_comap_eq_self_of_surjective hq]
  rw [hmaxmap]
  obtain ⟨t,h₁,h₂⟩ := hexchange
  have hex : (Paired.leftFactorMap Y e).range.map (MulAut.conj (t:H)).toMonoidHom =
      (Paired.rightFactorMap Y e).range := by
    rw [Paired.leftFactorMap_range,Paired.rightFactorMap_range,←map_map,←map_map,c.first_eq,c.second_eq]
    have hh := congrArg (map Y.subtype) h₁
    rw [map_map] at hh
    rw [map_map]
    exact hh
  have hex' : (Paired.rightFactorMap Y e).range.map (MulAut.conj (t:H)).toMonoidHom =
      (Paired.leftFactorMap Y e).range := by
    rw [Paired.rightFactorMap_range,Paired.leftFactorMap_range,←map_map,←map_map,c.second_eq,c.first_eq]
    have hh := congrArg (map Y.subtype) h₂
    rw [map_map] at hh
    rw [map_map]
    exact hh
  constructor
  · apply Paired.paired_first_factor_maximal R hp Y e (offender_generation R hp α hff hcore).2
      t t.property hex a
    intro x hx
    have hxS : x ∈ (baumann (T : Subgroup G)).map q := by
      rw [hS]
      obtain ⟨g,hg,rfl⟩ := hx
      exact ⟨(g,1),⟨hg,one_mem _⟩,rfl⟩
    exact map_mono (show baumann (T : Subgroup G) ≤ T from inf_le_left) hxS
  · apply Paired.paired_second_factor_maximal R hp Y e (offender_generation R hp α hff hcore).2
      t t.property hex' b
    intro x hx
    have hxS : x ∈ (baumann (T : Subgroup G)).map q := by
      rw [hS]
      obtain ⟨g,hg,rfl⟩ := hx
      exact ⟨(1,g),⟨one_mem _,hg⟩,rfl⟩
    exact map_mono (show baumann (T : Subgroup G) ≤ T from inf_le_left) hxS
end CFSG.Quasithin.ChapterE.ThompsonAction
