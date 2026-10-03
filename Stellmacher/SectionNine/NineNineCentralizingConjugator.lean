module
public import Stellmacher.SectionNine.NineNineFirstCenterIntersection
public import Stellmacher.SectionNine.NineNineTerminalIntersectionNormality
public import Stellmacher.SectionNine.NineNineCenterPlaneConjugator
public import Stellmacher.SectionNine.NineNineOutsideCenterConjugator
/-!
# The actual centralizing conjugator after Stellmacher (9.9)(3)

Under the same ambient distance-bound, reversed core containment, and
preceding-module index hypotheses as the terminal classification, there is
an element of the penultimate stabilizer centralizing the first center and
carrying the terminal vertex to the vertex two steps before it.

The actual first center is a line in the terminal/preterminal module
intersection. It differs from both neighboring center lines: the terminal
exclusion follows from the genuine initial transvection, while the other
exclusion follows from the preceding-module center noncontainment. If the
line lies in the middle center plane, the third neighbor's core supplies
the required centralizing swap. Otherwise the intersection is elementary of
order eight, lies in the middle core, and is normalized by its stabilizer.
The outside-center conjugator theorem corrects a neighbor mover by a core
translation fixing the selected line.

Every group and vertex is the actual one on the critical path. The supplied
ambient (9.8) bound remains explicit so callers can use the canonical theorem
without changing context or action instances. Source: Stellmacher (9.9),
printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`, the assertion
immediately following the center containment after (3).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_centralizing_conjugator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    ∃ y : G,
      y ∈ GAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ∧
      y ∈ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.firstStep : Set G) ∧
      ctx.Γ.act y ctx.criticalPath.a' = ctx.criticalPath.path
        ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let I := VAt Γ cp.a' ⊓ VAt Γ preterminal
  let R := ZAt Γ cp.firstStep
  let Z := ZAt Γ penultimate
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
  have hRcard : Nat.card R = 2 :=
    (nine_next_center_commutator_and_kernel ctx hshort cp.firstStep ⟨1,Γ.act_one _⟩).1
  have hRI : R ≤ I := nine_nine_first_center_le_terminal_intersection
    bound ctx hb hcore previous hprevious hne hlarge
  have hRterminal : R ≠ ZAt Γ cp.a' := fun heq =>
    nine_nine_first_center_not_le_terminal_center_of_initial_four ctx hshort hcore hfour heq.le
  have hRpreterminal : R ≠ ZAt Γ preterminal := by
    intro heq
    have hRZa : R ≤ ZAt Γ cp.a :=
      ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 cp.firstStep
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
    have hZaVprevious : ZAt Γ cp.a ≤ VAt Γ previous :=
      nine_seven_neighbor_center_le_module Γ
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprevious))
    exact nine_nine_preterminal_center_not_le_previous_module bound ctx hb hcore
      previous hprevious hne hlarge (heq ▸ hRZa.trans hZaVprevious)
  by_cases hRplane : R ≤ Z
  · exact nine_nine_center_plane_centralizing_conjugator ctx hshort R hRcard
      hRplane hRterminal hRpreterminal
  · have hIcard : Nat.card I = 8 := by
      have hh := (nine_nine_terminal_wreath_classification
        bound ctx hb hcore previous hprevious hne hlarge).2.2
      simpa only [show (2:ℕ)^3=8 from rfl] using hh
    obtain ⟨hZI,hIQ,hPI⟩ := nine_nine_terminal_intersection_core_normalized ctx hshort
    let _ : IsElementaryAbelian 2 (VAt Γ cp.a') :=
      (nine_three_second_extraction_inputs ctx.toLocalContext hshort).2.2.1
    have hIelem : IsElementaryAbelian 2 I := by
      refine {
        toIsMulCommutative := Subgroup.le_centralizer_iff_isMulCommutative.mp
          ((inf_le_left.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr
            (inferInstance : IsMulCommutative (VAt Γ cp.a')))).trans
              (Subgroup.centralizer_le inf_le_left))
        exponent_dvd_p := ?_ }
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro point
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := VAt Γ cp.a') (point:G) point.property.1)
    exact nine_nine_outside_center_centralizing_conjugator ctx hshort I hIcard hIelem
      hZI hIQ hPI R hRcard hRI hRplane

end Stellmacher.SectionNine
