module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The literal symmetric actor at a reciprocal vertex

Transport the original replacement marking through its injective realization
at a component vertex. Its kernel is the actual local two-core, and its
two-residual has image A₆. The resulting quotient equivalence agrees with
the same projection on every representative. SQTK is inherited from the
original pair through its replacement quotient.

This supplies the actor coordinates for recognizing the reciprocal FF
section in MS93 (5.12)(2), printed p.926, without changing its quotient map
or adding a local marking hypothesis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- One local projection, its induced quotient marking and the inherited
alternating SQTK hypothesis, all from the original replacement. -/
theorem reciprocal_vertex_actor_coordinates
    (hc : DistanceTwo.CentralLayer d) (a : Vertex d.radical)
    (ha : color d.radical a = false) :
    letI := Q_normal d.radical a
    ∃ π : (stabilizer d.radical a) →* Equiv.Perm (Fin 6),
      Function.Surjective π ∧
      π.ker = (Q d.radical a).subgroupOf (stabilizer d.radical a) ∧
      (pResidual 2 (stabilizer d.radical a)).map π = alternatingGroup (Fin 6) ∧
      ∃ E : ((stabilizer d.radical a) ⧸
          (Q d.radical a).subgroupOf (stabilizer d.radical a)) ≃* Equiv.Perm (Fin 6),
        (∀ g, E (QuotientGroup.mk' ((Q d.radical a).subgroupOf
          (stabilizer d.radical a)) g) = π g) ∧
        IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)) := by
  let := Q_normal d.radical a
  let := finite_stabilizer d.radical a
  obtain ⟨i,hi,hir,hiQ,_⟩ := vertex_coordinates (h := h) hc a ha
  let F : d.overgroup ≃* stabilizer d.radical a :=
    (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
  have hF (m : d.overgroup) : (F m : FreeAmalgam d.radical) = i m := rfl
  let π : (stabilizer d.radical a) →* Equiv.Perm (Fin 6) :=
    s.projection.comp F.symm.toMonoidHom
  have honto : Function.Surjective π := s.surjective.comp F.symm.surjective
  have hker : π.ker = (Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    ext g
    change s.projection (F.symm g) = 1 ↔ (g : FreeAmalgam d.radical) ∈ Q d.radical a
    rw [←MonoidHom.mem_ker,s.projection_kernel,←hiQ]
    constructor
    · intro hg
      refine ⟨F.symm g,hg,?_⟩
      rw [←hF,F.apply_symm_apply]
    · rintro ⟨m,hm,hmg⟩
      have he : F m = g := Subtype.ext (by rw [hF]; exact hmg)
      rw [←he,F.symm_apply_apply]
      exact hm
  have hres : (pResidual 2 (stabilizer d.radical a)).map π =
      alternatingGroup (Fin 6) := by
    rw [map_pResidual_of_surjective 2 π honto,Equiv.Perm.twoResidual_eq_alternating]
  let E : ((stabilizer d.radical a) ⧸
      (Q d.radical a).subgroupOf (stabilizer d.radical a)) ≃* Equiv.Perm (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π honto)
  refine ⟨π,honto,hker,hres,E,?_,?_⟩
  · intro g
    rfl
  · exact selected_alternating_sqtk s (h.sqtk.subgroup d.overgroup)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
