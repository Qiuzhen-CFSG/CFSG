module

public import Stellmacher.SectionNine.NineSixSmallModule
public import Stellmacher.SectionNine.NineNinePreviousClassification
public import Stellmacher.SectionNine.LemmaNineEight

/-!
# Terminal core containment cannot occur in the failed-index branch of (9.6)

For the original ambient (9.6) data at distance greater than three, assume
the index-two conclusion fails. The terminal module cannot be contained
in the first-step two-core.

The failed-index reduction gives first-module order sixteen and intersection
equal to the second center. A first-stabilizer element sending the second
vertex to the initial one transports that equality to a distinct backward
neighbor. Its module also has order sixteen, by initial-stabilizer local
transitivity, and its intersection has index four. Under terminal core
containment, the independently proved predecessor classification from the
proof of (9.9), supplied with the actual ambient (9.8) bound, forces that
same module to have order thirty-two, a contradiction.

This shortens the contained-core branch of Stellmacher (9.6), printed p.53
of `refs/files/stellmacher-n-group.pdf`, using the completed source (9.9)(3)
classification on printed p.56. That classification depends on (9.5),
(9.7), and (9.8), and is independent of (9.6); its explicit bound input is
discharged here. No numbered (9.9) conclusion or pending proof is used.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_six_terminal_core_exclusion
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hnot : ¬ QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep) : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 3 < cp.length := hb
  have hshort : 1 < cp.length := by change 3 < cp.length at hb;omega
  let second := cp.path ⟨2,by omega⟩
  have hsecond : IsCriticalPathOffset Γ cp 2 second := ⟨⟨2,by omega⟩,rfl,rfl⟩
  have hfirstSecond : Γ.adjacent cp.firstStep second := by
    have hh := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hh
    rwa [cp.path_first] at hh
  have hsecondThird : Γ.adjacent second third := by
    obtain ⟨index,hindex,rfl⟩ := hpath
    change index.val=3 at hindex
    have hh := cp.path_adj ⟨2,by omega⟩
    have heq : (⟨2,by omega⟩ : Fin cp.length).succ=index := Fin.ext (by simp;omega)
    rwa [heq] at hh
  have hfour : Nat.card (ZAt Γ cp.a)=4 :=
    (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
  have hbound := nine_six_first_module_card_le ctx.toLocalContext hshort hfour hquot
  have hcard : Nat.card (VAt Γ cp.firstStep)=16 :=
    nine_six_order_sixteen_of_not_index_two ctx.toLocalContext
      second third hsecond hpath hfour hbound hnot
  have hinter : VAt Γ cp.firstStep ⊓ VAt Γ third=ZAt Γ second :=
    nine_six_intersection_eq_center_of_not_index_two ctx.toLocalContext
      second third hsecond hpath hfour hbound hnot
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirstSecond)
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
  let previous := Γ.act (mover:G) third
  have hfix : Γ.act (mover:G) cp.firstStep=cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) (mover:G)).mp mover.property
  have hprevious : previous ∈ Neighborhood Γ cp.a := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    have hh := adjacent_act Γ (mover:G) hsecondThird
    rwa [hmove] at hh
  have hbackInter : VAt Γ previous ⊓ VAt Γ cp.firstStep=ZAt Γ cp.a := by
    have hh := congrArg (fun K : Subgroup G => K.map (MulAut.conj (mover:G)⁻¹).toMonoidHom) hinter
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (mover:G)⁻¹).injective,
      ← v_act,← v_act,← z_act,hfix,hmove,inf_comm] at hh
    exact hh
  have hne : previous ≠ cp.firstStep := by
    intro heq
    rw [heq,inf_idem] at hbackInter
    have hh := congrArg (fun K : Subgroup G => Nat.card K) hbackInter
    rw [hcard,hfour] at hh
    omega
  obtain ⟨align,halign⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have hpreviousCard : Nat.card (VAt Γ previous)=16 := by
    change Nat.card (v Γ previous)=16
    rw [← halign,v_act,Subgroup.card_map_of_injective (MulAut.conj (align:G)⁻¹).injective]
    exact hcard
  have hlarge : 4 * Nat.card (VAt Γ previous ⊓ VAt Γ cp.firstStep : Subgroup G) ≤
      Nat.card (VAt Γ previous) := by
    rw [hbackInter,hfour,hpreviousCard]
  have hclassification := nine_nine_previous_wreath_classification
    (fun shifted hcontain => lemma_nine_eight_ambient shifted hcontain)
    ctx hb hcore previous hprevious hne hlarge
  have hthirtyTwo : Nat.card (VAt Γ previous)=32 := by simpa using hclassification.1
  omega

end Stellmacher.SectionNine
