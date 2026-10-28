module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentGeometry
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Basic
/-!
# The original Sylow subgroup moves a centerless component

A Sylow two-subgroup cannot centralize a nonabelian quasisimple normal
factor: its intersection would be a trivial Sylow subgroup of an even
order group. The component commutator dichotomy then gives the whole
factor. This supplies movement in the actual source quotient.

Source: Aschbacher–Smith C.1.26, printed p.132.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
variable {H : Type*} [Group H] [Finite H]

theorem normal_quasisimple_factor_sylow_commutator
    (Y : Subgroup H) [Y.Normal] (A : Subgroup Y) [A.Normal] [IsQuasisimple A]
    (hz : center A = ⊥) (P : Sylow 2 Y) :
    ⁅A.map Y.subtype,(P : Subgroup Y).map Y.subtype⁆ = A.map Y.subtype := by
  let X := A.map Y.subtype
  let J := (P : Subgroup Y).map Y.subtype
  let e := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let : IsQuasisimple X := IsQuasisimple.of_mulEquiv e
  have hX : IsComponent H X := ⟨(inferInstance : A.Normal).isSubnormal.trans'
    (inferInstance : Y.Normal).isSubnormal,inferInstance⟩
  have hYX : Y ≤ normalizer (X : Set H) := by
    have hh := A.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hJX : J ≤ normalizer (X : Set H) := (map_subtype_le _).trans hYX
  have hn : ⁅X,J⁆ ≠ ⊥ := by
    intro he
    have hc : J ≤ centralizer (X : Set H) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    obtain ⟨S,hS⟩ := P.exists_sylow_map_eq_inf_of_normal A
    have hs : (S : Subgroup A) = ⊥ := by
      apply bot_unique
      intro p hp
      have hpP : (p:Y) ∈ (P : Subgroup Y) := (hS.le (mem_map_of_mem A.subtype hp)).1
      have hpJ : ((p:Y):H) ∈ J := mem_map_of_mem Y.subtype hpP
      have hpz : p ∈ center A := by
        rw [mem_center_iff]
        intro a
        exact Subtype.ext (Subtype.ext (hc hpJ a (mem_map_of_mem Y.subtype a.property)))
      exact hz.le hpz
    apply S.not_dvd_index
    rw [hs,index_bot]
    exact ChapterA.SQTKStructure.OrdinarySource.even_of_quasisimple A
  rcases hX.commutator_dichotomy J with hb | he
  · exact (hn hb).elim
  · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hJX)
      ((le_iSup_conjugates X J).trans he.symm.le)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
