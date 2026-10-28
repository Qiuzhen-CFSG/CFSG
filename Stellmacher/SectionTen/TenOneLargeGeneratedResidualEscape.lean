module
public import Stellmacher.SectionTen.TenOneLargeFirstResidualIndex
public import Stellmacher.SectionTen.TenOneCommonIntersection

/-!
# The terminal residual core moves the generated subgroup beyond the common intersection

In the actual Section Ten no-transvection case, the commutator of the
generated subgroup W with the terminal residual two-core U is not contained
in the common first/terminal module intersection I. The same hypotheses imply
that the derived subgroup of U is not contained in the middle center. No
source-(17) index, source-(18) cardinality, or Frobenius quotient is assumed.

Source (15) gives an order-sixteen first seed inside W, containing the
order-eight common intersection. If [W,U] lay in that intersection, U would
normalize the seed. The actual cubic action of U fixes the terminal neighbor
and sends the first neighbor to the third. Hence that same seed would lie
in two distinct neighbor modules, whose intersection is I of order eight,
a contradiction. Since W lies in U and the middle center lies in I, this
also excludes centrality of the full derived subgroup of U there.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.64,
the residual-derived contradiction preceding (19). This geometric proof
uses the checked source-(14)/(15) facts and the original graph; it does not
use the incompatible printed centralizer equality in (16).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_generated_residual_commutator_escape
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let W := conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)
    ¬ ⁅W,twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ cp.firstStep
  let V := VAt Γ cp.a'
  let U := twoCoreIn (EAt Γ cp.a')
  let I := A ⊓ V
  let seed := A ⊓ QAt Γ cp.a'
  let W := conjugateClosure seed (GAt Γ middle)
  change ¬ ⁅W,U⁆ ≤ I
  intro hcomm
  obtain ⟨_,hfirst,hterminal,hends⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨_,hVcard,hIcard⟩ := ten_one_large_terminal_structure ctx middle hpath hno
  have hAcard : Nat.card A=32 := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle
      ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    change Nat.card (v Γ cp.a')=32 at hVcard
    rw [←hmove,v_act,card_map_of_injective (MulAut.conj (mover:G)⁻¹).injective] at hVcard
    exact hVcard
  obtain ⟨hres,hWU⟩ := ten_one_large_first_residual_index ctx middle hpath hno
  have hseedW : seed≤W := by
    intro x hx
    exact Subgroup.subset_closure ⟨(1:GAt Γ middle),⟨x,hx⟩,by simp⟩
  have hUQ : U≤QAt Γ cp.a' := by
    change twoCoreIn (Γ.twoResidualAt cp.a')≤Γ.twoCoreAt cp.a'
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hseedEq : seed=A⊓U := le_antisymm
    (le_inf inf_le_left (hseedW.trans hWU)) (inf_le_inf_left A hUQ)
  have hseedCard : Nat.card seed=16 := by
    change Nat.card A=2*Nat.card (A⊓U:Subgroup G) at hres
    rw [←hseedEq,hAcard] at hres
    omega
  have hVQ : V≤QAt Γ cp.a' :=
    neighbor_join_le_core_of_length_gt_one Γ cp (by change 1<ctx.criticalPath.length; rw [ctx.critical_length]; decide) cp.a'
  have hIseed : I≤seed := inf_le_inf_left A hVQ
  have hUN : U≤normalizer (seed:Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hseedW le_rfl).trans hcomm).trans hIseed)
  have hUP : U≤GAt Γ cp.a' := by
    change twoCoreIn (Γ.twoResidualAt cp.a')≤Γ.stabilizer cp.a'
    rw [Γ.twoResidualAt_def]
    exact (twoCoreIn_le _).trans (twoResidualIn_le _)
  have hUedge : U≤GAt Γ middle⊓GAt Γ cp.a' := le_inf
    (hUQ.trans (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) default).2.2)) hUP
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hescape := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext cp.a' middle
      ⟨alignment,halignment⟩ (Γ.adjacent_symm hterminal)
  have hcubic := cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven middle
    (sectionTenOpeningData ctx middle hpath).quotient_model
  let Neighbors := {neighbor : Γ.Vertex // Γ.adjacent middle neighbor}
  let _ : Finite Γ.Vertex := Γ.finiteVertex
  have hthree : 3≤ENat.card Neighbors := by
    rw [ENat.card_eq_coe_natCard,hcubic.degree]
    norm_num
  obtain ⟨third,hthirdFirst,hthirdTerminal⟩ := ENat.exists_ne_ne_of_three_le hthree
    (⟨cp.firstStep,hfirst⟩:Neighbors) (⟨cp.a',hterminal⟩:Neighbors)
  have hthirdFirst' : (third:Γ.Vertex)≠cp.firstStep := fun heq => hthirdFirst (Subtype.ext heq)
  have hthirdTerminal' : (third:Γ.Vertex)≠cp.a' := fun heq => hthirdTerminal (Subtype.ext heq)
  obtain ⟨actor,hmove⟩ := hcubic.punctured_transitivity cp.a' hterminal U hUedge hescape
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr hfirst,hends⟩
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr third.property,hthirdTerminal'⟩
  change Γ.act (actor:G) cp.firstStep=(third:Γ.Vertex) at hmove
  have hmap : seed.map (MulAut.conj (actor:G)⁻¹).toMonoidHom=seed :=
    mem_normalizer_iff_map_conj_eq.mp (hUN (U.inv_mem actor.property))
  have hseedThird : seed≤VAt Γ third := by
    have hm := map_mono (f:=(MulAut.conj (actor:G)⁻¹).toMonoidHom)
      (show seed≤A from inf_le_left)
    rw [hmap] at hm
    change seed≤v Γ third
    rw [←hmove,v_act]
    exact hm
  have hseedI : seed≤I := by
    change seed≤VAt ctx.Γ ctx.criticalPath.firstStep⊓VAt ctx.Γ ctx.criticalPath.a'
    rw [←ten_one_neighbor_intersection ctx middle hpath hfirst third.property hthirdFirst'.symm]
    exact le_inf inf_le_left hseedThird
  have hh := card_le_of_le hseedI
  change Nat.card seed≤Nat.card I at hh
  change Nat.card I=8 at hIcard
  rw [hseedCard,hIcard] at hh
  omega

public theorem ten_one_large_terminal_residual_derived_not_le_middle_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ¬ ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'),twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆ ≤
      ZAt ctx.Γ middle := by
  intro hderived
  apply ten_one_large_generated_residual_commutator_escape ctx middle hpath hno
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  exact ((commutator_mono (ten_one_large_first_residual_index ctx middle hpath hno).2 le_rfl).trans
    hderived).trans (le_inf
      (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
      (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal)))

end Stellmacher.SectionTen
