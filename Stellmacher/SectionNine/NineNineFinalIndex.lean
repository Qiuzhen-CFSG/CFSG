module
public import Stellmacher.SectionNine.NineNineTerminalNormalizerIndex
public import Stellmacher.SectionNine.NineNineCentralizingConjugator
public import Theory.GroupTheory.TwoGroupIndexThree

/-!
# The final index-two intersection in Stellmacher (9.9)

The preceding module intersects the penultimate stabilizer with index exactly
two, under the original explicit distance-bound and large-index inputs.
The actual centralizing conjugator carries the terminal normalizer to its
preterminal counterpart and fixes the penultimate stabilizer, so the proved
relative index three transports unchanged.

The preceding module fixes the first-center line and normalizes the
preterminal line because it lies in the preterminal stabilizer. It therefore
lies in that normalizer. A finite two-subgroup meets an ambient index-three
subgroup with index at most two. The previously proved penultimate escape
excludes index one, giving the exact cardinality relation used in the final
commutator contradiction.

Source: Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`, the conclusion of the normalizer paragraph.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_final_index_two
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
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous))
 : QuotientCardEq (VAt ctx.Γ previous)
      (VAt ctx.Γ previous ⊓ GAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let R := ZAt Γ cp.firstStep
  let B := VAt Γ previous
  let X := GAt Γ cp.a' ⊓ Subgroup.normalizer (R⊔ZAt Γ cp.a' : Subgroup G)
  let Y := GAt Γ preterminal ⊓ Subgroup.normalizer (R⊔ZAt Γ preterminal : Subgroup G)
  let P := GAt Γ penultimate
  have hshort : 1<cp.length := by change 3<cp.length at hb; omega
  have hindex := nine_nine_terminal_normalizer_index_three bound ctx hb hcore previous hprevious hne hlarge
  change P.relIndex X=3 at hindex
  obtain ⟨y,hyP,hyR,hyt⟩ := nine_nine_centralizing_conjugator bound ctx hb hcore previous hprevious hne hlarge
  have hXmap : X.map (MulAut.conj y⁻¹).toMonoidHom=Y := by
    have hh := nine_nine_normalizer_conjugation Γ cp.a' R y hyR
    rw [hyt] at hh
    exact hh
  have hPmap : P.map (MulAut.conj y⁻¹).toMonoidHom=P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer (P.inv_mem hyP))
  have hYindex : P.relIndex Y=3 := by
    rw [← hXmap,← hPmap,Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hindex
  have hBpre : B≤GAt Γ preterminal := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    have hlong : 4<cp.length := by
      obtain ⟨n,hn⟩ := hodd
      change 3<cp.length at hb
      omega
    exact (nine_eight_v_le_generated_neighborhood Γ hprevious).trans
      (nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
  have hBR : B≤Subgroup.normalizer (R : Set G) :=
    nine_nine_previous_normalizes_first_center ctx.toLocalContext hb previous hprevious
  have hBZpre : B≤Subgroup.normalizer (ZAt Γ preterminal : Set G) :=
    hBpre.trans (stabilizer_le_normalizer_z Γ preterminal)
  have hBY : B≤Y := by
    refine le_inf hBpre ?_
    intro mover hmover
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hRmap : R.map (MulAut.conj mover).toMonoidHom=R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBR hmover)
    have hZmap : (ZAt Γ preterminal).map (MulAut.conj mover).toMonoidHom=ZAt Γ preterminal :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBZpre hmover)
    change (R⊔ZAt Γ preterminal).map (MulAut.conj mover).toMonoidHom=R⊔ZAt Γ preterminal
    rw [Subgroup.map_sup,hRmap,hZmap]
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have htwo : IsPGroup 2 B := by
    change IsPGroup 2 (v Γ previous)
    rw [← hmover,v_act]
    let _ := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
    exact (IsElementaryAbelian.isPGroup 2 (v Γ cp.firstStep)).map _
  have hbound := Subgroup.two_group_relIndex_le_two_of_relIndex_three B P Y htwo hBY hYindex
  have hnot : ¬ B≤P := nine_nine_previous_not_le_penultimate_stabilizer
    ctx hb hcore previous hprevious hne hlarge
  have hindexTwo : P.relIndex B=2 := by
    have hpos : 0<P.relIndex B := by
      change 0<Nat.card (B ⧸ P.subgroupOf B)
      exact Nat.card_pos
    have hneOne : P.relIndex B≠1 := fun heq => hnot (Subgroup.relIndex_eq_one.mp heq)
    omega
  have hcount := ((B⊓P).subgroupOf B).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show B⊓P≤B from inf_le_left)).toEquiv] at hcount
  change (B⊓P).relIndex B*Nat.card (B⊓P : Subgroup G)=Nat.card B at hcount
  rw [Subgroup.inf_relIndex_left,hindexTwo] at hcount
  exact hcount.symm

end Stellmacher.SectionNine
