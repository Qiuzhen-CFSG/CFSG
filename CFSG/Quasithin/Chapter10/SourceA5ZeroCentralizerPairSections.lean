module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerSection
public import CFSG.Quasithin.Chapter10.SourceA5CentralizerSectionConjugation
public import Theory.GroupTheory.SubgroupImageSection

/-!
# Literal quotient sections for both original factor centralizers

The proved natural-kernel splitting of the first actual factor centralizer
is converted to a section of its original quotient image. Conjugating the
commuting diagram by the prescribed original Sylow element supplies the
second factor section. Thus both original centralizers split over the
same ambient quotient without an additional extension premise.
Source: Aschbacher–Smith10.2.1, pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

theorem source_a5_zero_centralizer_image_section
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    OriginalCentralizerImageSection D (L.subgroupOf (localJoin T L)) := by
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  obtain ⟨d,c,f,_,hfk,_,σ,hσ⟩ := source_a5_zero_centralizer_symmetric_section D e hn hout hz
  exact exists_image_section_of_ker_eq _ _ f hfk σ hσ

theorem source_a5_zero_centralizer_pair_sections
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
      L.subgroupOf (localJoin T L) ≠
        (L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom ∧
      SourceOriginalPairedOpposite D t ∧
      OriginalCentralizerImageSection D (L.subgroupOf (localJoin T L)) ∧
      OriginalCentralizerImageSection D
        ((L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom) :=
  source_a5_zero_centralizer_pair_sections_of_first D e hn hout hz
    (source_a5_zero_centralizer_image_section D e hn hout hz)
end CFSG.Quasithin.Chapter10
