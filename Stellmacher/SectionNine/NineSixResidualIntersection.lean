module

public import Stellmacher.SectionNine.NineSixResidualNoncontainment
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore

/-!
# The residual intersection in the order-sixteen branch of (9.6)

In the ambient Section Nine geometry, assume the first core quotient is
SL₂(2), the critical path has length greater than one, and the first module
has order sixteen. Then the intersection of the initial center with the
first residual commutator lies in the first center.

The proved source (*) noncontainment makes this intersection proper in the
order-four initial center. Both terms are invariant under the first core.
A nontrivial proper intersection has index two, so the induced quotient
action is trivial and it contains the known core commutator, the order-two
first center. Equality follows from the orders. The trivial intersection
is immediate. This is the transfer used at the terminal edge of the
length-three exclusion.

Source: Stellmacher (9.6), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_six_initial_center_residual_intersection_le_next_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 16) :
    ZAt ctx.Γ ctx.criticalPath.a ⊓
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let U := VAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let D := ⁅U,E⁆
  let Z := ZAt Γ cp.a
  let K := Z ⊓ D
  have hZcard : Nat.card Z = 4 := (lemma_nine_three_ambient ctx hb cp.a
    ⟨1, Γ.act_one _⟩).2
  have hlineCard := (nine_next_center_commutator_and_kernel ctx hb cp.firstStep
    ⟨1,Γ.act_one _⟩).1
  have hnot : ¬ Z ≤ D :=
    nine_six_initial_center_not_le_first_residual_commutator ctx hb hquot hcard
  have hlt : K < Z := lt_of_le_of_ne inf_le_left (by
    intro heq
    exact hnot (heq.ge.trans inf_le_right))
  have hKlt : Nat.card K < 4 := by
    rw [← hZcard]
    exact lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le) (by
      intro heq
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le heq.ge))
  have hdvd : Nat.card K ∣ 4 := hZcard ▸ Subgroup.card_dvd_of_le hlt.le
  have hpos := Nat.card_pos (α := K)
  have hcases : Nat.card K = 1 ∨ Nat.card K = 2 := by
    interval_cases h : Nat.card K <;> norm_num at *
  rcases hcases with hKcard | hKcard
  · exact (Subgroup.card_eq_one.mp hKcard).le.trans bot_le
  have hQP : Q ≤ P := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp
    change ((Γ.twoResidualAt cp.firstStep).subgroupOf P).Normal
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_normal _
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (stabilizer_le_normalizer_v Γ cp.firstStep hactor),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPE hactor)]
  have hQZ : Q ≤ Subgroup.normalizer (Z : Set G) :=
    (((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans
      (edge_sylow_data ctx.sectionSeven Γ cp).1.1).trans
        (stabilizer_le_normalizer_z Γ cp.a))
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Z ⊓ D).map (↑(MulAut.conj actor) : G →* G) = Z ⊓ D
    rw [Subgroup.map_inf _ _ _ (MulAut.conj actor).injective,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQZ hactor),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPD (hQP hactor))]
  have hindex : K.relIndex Z = 2 := by
    have hprod := (K.subgroupOf Z).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlt.le).toEquiv,
      hKcard, hZcard] at hprod
    change K.relIndex Z * 2 = 4 at hprod
    omega
  have hline : ZAt Γ cp.firstStep ≤ K := by
    have hcomm : ⁅Z,Q⁆ = ZAt Γ cp.firstStep :=
      nine_initial_next_core_commutator_of_initial_four ctx.toLocalContext hZcard
    exact hcomm.ge.trans
      (SectionEight.commutator_le_of_normalizing_index_two Z K Q hindex hQZ hQK)
  exact (Subgroup.eq_of_le_of_card_ge hline (by
    rw [hKcard, hlineCard])).ge

end Stellmacher.SectionNine
