module
public import Stellmacher.SectionNine.NineNineSupportData
public import Stellmacher.SectionNine.NineNineSupportTransport
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineNextCenterCommutator

/-!
# The maximal commutator-bounded subgroup in Stellmacher (9.9)

For a support in the first-step core whose commutator with the initial
center is exactly the first-step center, the largest subgroup of a distinct
neighbor module with support commutator in that center is the intersection
of the two neighbor modules. The one-sided containment only requires the
support to lie in the initial edge stabilizer, and is also exported for (9.8).
The critical distance is greater than three,
so the predecessor module normalizes the first-step center.

Both adjacent center lines belong to the maximal subgroup A. The neighboring
core normalizes A because its commutator lies in the predecessor center;
the support normalizes A because its commutator lies in the first-step center.
The proved cubic transporter in their join carries the predecessor vertex
to the first step. Transporting A's containment in the predecessor module
therefore puts it in the first-step module. The reverse inclusion follows
from the known first-step module/core commutator. This proves directly the
consequence of the source's residual-generation argument needed here.

Source: Stellmacher (9.9), the maximal subgroup A between relations (1)
and (2), printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_maximal_le_intersection_of_edge
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (support : Subgroup G)
    (hsupport : support ≤ GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hcomm : ⁅support, ZAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep) :
    nineNineCommutatorBound (VAt ctx.Γ previous) support
      (ZAt ctx.Γ ctx.criticalPath.firstStep)
      (nine_nine_previous_normalizes_first_center ctx.toLocalContext hb
        previous hprevious) ≤
      VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Vprev := VAt Γ previous
  let Vfirst := VAt Γ cp.firstStep
  let Zprev := ZAt Γ previous
  let R := ZAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let Qprev := QAt Γ previous
  let A := nineNineCommutatorBound Vprev support R
    (nine_nine_previous_normalizes_first_center ctx.toLocalContext hb previous hprevious)
  have hA : A ≤ Vprev ∧ ⁅A, support⁆ ≤ R :=
    (le_nineNineCommutatorBound_iff _ _ _ _ _).mp le_rfl
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1, Γ.act_one _⟩).2
  have hsplit := nine_three_center_split ctx hshort ⟨1, Γ.act_one _⟩
    ((mem_neighborhood_iff_adjacent Γ).mp hprevious) cp.firstStep_adj hne
  have hZa : Za = Zprev ⊔ R := hsplit.1
  have hZprevZa : Zprev ≤ Za := le_sup_left.trans_eq hZa.symm
  have hRZa : R ≤ Za := le_sup_right.trans_eq hZa.symm
  have hZaPrev : Za ≤ Vprev :=
    nine_seven_neighbor_center_le_module Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprevious))
  have hRPrev : R ≤ Vprev := hRZa.trans hZaPrev
  have hRA : R ≤ A := by
    apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
    refine ⟨hRPrev, ?_⟩
    have hh := Subgroup.commutator_mono hRZa (le_refl support)
    rw [Subgroup.commutator_comm Za support, hcomm] at hh
    exact hh
  obtain ⟨aligner, haligner⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.a ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have horbit : IsConjugateVertex Γ cp.firstStep previous := ⟨aligner, haligner⟩
  have hprevComm : ⁅Vprev, Qprev⁆ = Zprev :=
    (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour previous horbit).2
  have hQprevP : Qprev ≤ GAt Γ previous := by
    change Γ.twoCoreAt previous ≤ GAt Γ previous
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZprevVprev : Zprev ≤ Vprev := by
    rw [← hprevComm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQprevP.trans (stabilizer_le_normalizer_v Γ previous))
  have hZprevA : Zprev ≤ A := by
    apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
    refine ⟨hZprevVprev, ?_⟩
    have hh := Subgroup.commutator_mono hZprevZa (le_refl support)
    rw [Subgroup.commutator_comm Za support, hcomm] at hh
    exact hh
  have hQnormalize : Qprev ≤ Subgroup.normalizer (A : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact ((Subgroup.commutator_mono hA.1 (le_refl Qprev)).trans_eq hprevComm).trans hZprevA
  have hVnormalize : support ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hA.2.trans hRA)
  obtain ⟨mover, hmover, hmove⟩ := nine_nine_support_transporter_of_edge
    ctx hshort previous hprevious hne support hsupport hcomm
  have hmoverN : mover ∈ Subgroup.normalizer (A : Set G) :=
    (sup_le hQnormalize hVnormalize) hmover
  have hmapA : A.map (MulAut.conj mover⁻¹).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (A : Set G)).inv_mem hmoverN)
  have hmap := Subgroup.map_mono (f := (MulAut.conj mover⁻¹).toMonoidHom) hA.1
  change A.map _ ≤ (v Γ previous).map _ at hmap
  rw [hmapA, ← v_act, hmove] at hmap
  exact le_inf hA.1 hmap

public theorem nine_nine_maximal_eq_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (support : Subgroup G)
    (hsupport : support ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hcomm : ⁅support, ZAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep) :
    nineNineCommutatorBound (VAt ctx.Γ previous) support
      (ZAt ctx.Γ ctx.criticalPath.firstStep)
      (nine_nine_previous_normalizes_first_center ctx.toLocalContext hb
        previous hprevious) =
      VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep := by
  have hfirstCoreA : QAt ctx.Γ ctx.criticalPath.firstStep ≤
      GAt ctx.Γ ctx.criticalPath.a :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
      ctx.criticalPath.firstStep ctx.criticalPath.a
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)) default).2.2
  have hfirstCoreSelf : QAt ctx.Γ ctx.criticalPath.firstStep ≤
      GAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  apply le_antisymm (nine_nine_maximal_le_intersection_of_edge ctx hb support
    (le_inf (hsupport.trans hfirstCoreA) (hsupport.trans hfirstCoreSelf)) hcomm
    previous hprevious hne)
  apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
  refine ⟨inf_le_left, ?_⟩
  have hfour := (lemma_nine_three_ambient ctx (by omega) ctx.criticalPath.a
    ⟨1, ctx.Γ.act_one _⟩).2
  have hfirstComm := (nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour ctx.criticalPath.firstStep ⟨1, ctx.Γ.act_one _⟩).2
  exact (Subgroup.commutator_mono inf_le_right hsupport).trans_eq hfirstComm

end Stellmacher.SectionNine