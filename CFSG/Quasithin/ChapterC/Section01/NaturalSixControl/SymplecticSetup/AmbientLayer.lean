module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.AlternatingOffenders
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# The actual central omega layer is an FF-module

The native natural submodule identifies the centralizer of the full omega
center of the two-core with that two-core. MS3 forces the elementary
Thompson subgroup of the edge group outside this kernel. Hence the literal
quotient action on the central omega layer has an FF-offender. This proof
retains the specified map into S6 and does not split a central extension.

Source: MS93 (3.2), printed pp.861--863.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- The original central omega layer, before embedding in the graph. -/
abbrev ambientX : Subgroup M := omegaCenter (pCore 2 M)

theorem X_alpha_eq : X R (alpha R) = (ambientX (M := M)).map (embedM R) := by
  rw [X,Q_alpha R s.two_group s.core_le,omegaCenter_map _ _ (embedM_injective R)]

theorem module_le_ambientX : W ≤ ambientX (M := M) := by
  apply (map_le_map_iff_of_injective (embedM_injective R)).mp
  rw [← s.X_alpha_eq]
  exact s.module_le_Z.trans s.Z_le_X

theorem ambientX_normal : (ambientX (M := M)).Normal := by
  constructor
  intro x hx g
  apply (mem_map_iff_mem (embedM_injective R)).mp
  rw [← s.X_alpha_eq]
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [show alpha R = mVertex R 1 from rfl,stabilizer_m_base]
    exact ⟨g,rfl⟩
  have hx' : embedM R x ∈ X R (alpha R) := by
    rw [s.X_alpha_eq]
    exact mem_map_of_mem _ hx
  have hc := le_normalizer_iff.mp (X_normalized R (alpha R)) _ hg _ hx'
  simpa only [map_mul,map_inv] using hc

theorem ambientX_centralizer : centralizer (ambientX (M := M) : Set M) = pCore 2 M := by
  apply le_antisymm
  · exact (centralizer_le s.module_le_ambientX).trans_eq s.module_centralizer
  · intro q hq x hx
    exact ((mem_omegaCenter_iff.mp hx).2.2 q hq).symm

theorem ambientX_kernel : s.projection.rangeRestrict.ker =
    centralizer (ambientX (M := M) : Set M) := by
  rw [MonoidHom.ker_rangeRestrict,s.projection_kernel,s.ambientX_centralizer]

theorem ambientX_isFFModule :
    letI := s.ambientX_normal
    letI := omegaCenter_elementary (pCore 2 M)
    IsFFModule (NormalElementaryQuotient.representation (ambientX (M := M))
      s.projection.rangeRestrict s.projection.rangeRestrict_surjective s.ambientX_kernel) := by
  let := s.ambientX_normal
  let := omegaCenter_elementary (pCore 2 M)
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le
    (ambientX (M := M)) s.projection.rangeRestrict
    s.projection.rangeRestrict_surjective s.ambientX_kernel R
  · exact (omegaCenter_le (pCore 2 M)).trans s.core_le
  · simpa only [MonoidHom.ker_rangeRestrict,s.projection_kernel] using s.thompson_not_le_core

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
