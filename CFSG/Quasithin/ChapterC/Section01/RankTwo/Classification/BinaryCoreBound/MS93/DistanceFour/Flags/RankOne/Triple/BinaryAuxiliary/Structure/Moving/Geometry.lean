module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Comparison

/-!
# Geometric inputs for the moving auxiliary factor on MS93 p.907

The core-action calculation proves that the actual two-core fixes Y/U.
The midpoint Sylow arrangement supplies an incident flag at which the original
second layer lies in the transported full actor and escapes its core. The
source nonzero triple and nontriviality of Y/U are also retained.

The reverse commutator-index comparison and the nontrivial action of the
residual on Y/U remain separate obligations. Neither is asserted by the
selection theorem below.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed pp.906--907.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Select the actual incident actor, retaining its containment and core escape.
The containment comes from the existing Sylow subgroup's ambient image. -/
theorem exists_middle_actor (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    ∃ e : M, flagIncident source i 1 e ∧
      secondFlagLayer source i p.delta0 ≤
        (localFlagActor source (!i) e).map t.conjugation.toMonoidHom ∧
      ¬ secondFlagLayer source i p.delta0 ≤
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom := by
  obtain ⟨e, he, hn, S, hS⟩ :=
    exists_middle_sylow source geometry hlarge i hkernel p t
  refine ⟨e, he, ?_, hn⟩
  have himage := map_le_range (f :=
    ((localFlagActor source (!i) e).map t.conjugation.toMonoidHom).subtype)
    (S : Subgroup ((localFlagActor source (!i) e).map t.conjugation.toMonoidHom))
  rw [hS, range_subtype] at himage
  exact le_sup_left.trans himage

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
