module
public import Stellmacher.SectionTen.TenOneLargeCentralizerAction
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# Residual action on the first module centralizer

In the actual no-transvection Section Ten context, the first residual
centralizes the first module centralizer inside the first two-core modulo
the first module. Only the original context, middle vertex, path offset
and no-transvection hypothesis are used.

Choose an element of the middle stabilizer sending the first neighbor to
the terminal neighbor. Conjugation transports the first module, two-core
and residual simultaneously. The image of its module centralizer lies in
the terminal module centralizer, so the proved terminal commutator bound
applies. Injectivity returns the required first-side bound. The original
terminal theorem is used before this subgroup transport, so no new
critical-path context or transported no-transvection premise is needed.

Source: Stellmacher (10.1)(20), Journal of Algebra 190 (1997), printed p.65,
using the conjugate of the terminal centralizer bound preceding (16), p.64.
This is the first-side input for restricting that bound to the actual
centralizer of the terminal residual two-core.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u

public theorem ten_one_large_first_centralizer_residual_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ⁅QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G),
      EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
  let equiv := MulAut.conj (mover : G)⁻¹
  have hVmap : (VAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom =
      VAt ctx.Γ ctx.criticalPath.a' := by
    change (v ctx.Γ ctx.criticalPath.firstStep).map _ = v ctx.Γ ctx.criticalPath.a'
    rw [←v_act,hmove]
  have hQmap : (QAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom =
      QAt ctx.Γ ctx.criticalPath.a' := by
    change (q ctx.Γ ctx.criticalPath.firstStep).map _ = q ctx.Γ ctx.criticalPath.a'
    rw [←q_act,hmove]
  have hEmap : (EAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom =
      EAt ctx.Γ ctx.criticalPath.a' := by
    change (ctx.Γ.twoResidualAt _).map _ = ctx.Γ.twoResidualAt _
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoResidualAt_def]
    change (twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.firstStep)).map _ =
      twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')
    rw [←hmove,stabilizer_act,conjugateBy,twoResidualIn_map_equiv]
  have hCmap : (Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.firstStep : Set G)).map equiv.toMonoidHom ≤
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) := by
    have hh := Subgroup.map_centralizer_le_centralizer_image
      (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) equiv.toMonoidHom
    change _ ≤ Subgroup.centralizer
      ((VAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom : Set G) at hh
    rwa [hVmap] at hh
  apply (Subgroup.map_le_map_iff_of_injective (f := equiv.toMonoidHom) equiv.injective).mp
  rw [Subgroup.map_commutator,Subgroup.map_inf _ _ _ equiv.injective,hQmap,hEmap,hVmap]
  exact (Subgroup.commutator_mono (inf_le_inf_left _ hCmap) le_rfl).trans
    (ten_one_large_centralizer_residual_commutator ctx middle hpath hno)

end Stellmacher.SectionTen
