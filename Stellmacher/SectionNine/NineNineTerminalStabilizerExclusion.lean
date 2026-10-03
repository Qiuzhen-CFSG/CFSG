module
public import Stellmacher.SectionNine.NineNineSupportProducer
public import Stellmacher.SectionNine.NineNineMaximalIntersection
public import Theory.GroupTheory.FourQuotientCommutatorKernel

/-!
# The terminal-stabilizer exclusion in (9.9)

Assume the terminal module is contained in the first-step core and that
`V_{a-1}` has intersection index at least four with `V_1`.  The order-four
quotient support supplied by the rank-one factor yields a subgroup of index at
most two in `V_{a-1}` whose commutator with the support is in `Z_1`.  The
maximal-commutator identification from the preceding part of (9.9) places this
subgroup in `V_{a-1} ∩ V_1`, contradicting the index hypothesis.  This is the
first exclusion on printed page 56 and is kept as an explicit ambient lemma for
the remaining geometric reductions.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_previous_not_le_terminal_stabilizer_of_large_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    ¬ VAt ctx.Γ previous ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  intro hcontained
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let B := VAt Γ previous
  let U := VAt Γ cp.a'
  let R := ZAt Γ cp.firstStep
  let Z := ZAt Γ cp.a'
  let Za := ZAt Γ cp.a
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨support, hsupport, hZsupport, hcardSupport, hRsupport, hcomm, hcontrol⟩ :=
    nine_nine_support_data_with_line_of_terminal_core ctx hshort hcore
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1, Γ.act_one _⟩).2
  have hRcard : Nat.card R = 2 :=
    (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour
      cp.firstStep ⟨1, Γ.act_one _⟩).1
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hterminalOrbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨mover, hmover⟩
  have hZcard : Nat.card Z = 2 :=
    (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour
      cp.a' hterminalOrbit).1
  have hRnot : ¬ R ≤ Z := nine_nine_first_center_not_le_terminal_center_of_initial_four
    ctx hshort hcore hfour
  have hZnot : ¬ Z ≤ R := by
    intro hle
    exact hRnot (Subgroup.eq_of_le_of_card_ge hle (by omega)).ge
  obtain ⟨fixed, hfixedZ, hfixedR⟩ := Set.not_subset.mp hZnot
  have hRU : R ≤ U := hRsupport.trans hsupport
  have hUZa : U ≤ Subgroup.normalizer (Za : Set G) := by
    have hh := (nine_nine_terminal_action_of_core ctx.toLocalContext hcore).2.1
    change VAt ctx.Γ cp.a' ≤ Subgroup.normalizer (ZAt ctx.Γ cp.a : Set G) at hh
    exact hh
  have hRZa : R ≤ Za := by
    change ⁅support, Za⁆ = R at hcomm
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hsupport.trans hUZa)
  have hlong := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort
  let _ : IsElementaryAbelian 2 U :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hshort).2.2.1
  have hUab : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hN : (R.subgroupOf support).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRsupport).mpr
      (hsupport.trans (hUab.trans ((Subgroup.centralizer_le hRU).trans
        (Subgroup.centralizer_le_normalizer _))))
  obtain ⟨aligner, haligner⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.a ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  let _ : IsElementaryAbelian 2 B := by
    change IsElementaryAbelian 2 (v Γ previous)
    rw [← haligner, v_act]
    let _ : IsElementaryAbelian 2 (v Γ cp.firstStep) := hlong.1
    exact IsElementaryAbelian.map (MulAut.conj (aligner : G)⁻¹).toMonoidHom
  have hBab : B ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hZaB : Za ≤ B := nine_seven_neighbor_center_le_module Γ
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprevious))
  have hBZa : B ≤ Subgroup.centralizer (Za : Set G) :=
    hBab.trans (Subgroup.centralizer_le hZaB)
  have hBR : B ≤ Subgroup.normalizer (R : Set G) :=
    hBZa.trans ((Subgroup.centralizer_le hRZa).trans (Subgroup.centralizer_le_normalizer _))
  have hBS : B ≤ Subgroup.normalizer (support : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact ((Subgroup.commutator_mono (le_refl support)
      (le_inf hcontained hBZa)).trans hcontrol).trans (sup_le hRsupport hZsupport)
  have hcardR : Nat.card support = 4 * Nat.card R := by
    change Nat.card support = 4 * Nat.card Z at hcardSupport
    change Nat.card R = 2 at hRcard
    change Nat.card Z = 2 at hZcard
    omega
  have hfixed : B ≤ Subgroup.centralizer ({fixed} : Set G) :=
    hcontained.trans ((nine_next_center_centralizes_stabilizer ctx.toLocalContext
      cp.a' hterminalOrbit).trans (Subgroup.centralizer_le
        (show ({fixed} : Set G) ⊆ (Z : Set G) from fun x hx =>
        (Set.mem_singleton_iff.mp hx) ▸ hfixedZ)))
  obtain ⟨C, hCB, hCcard, hCcomm⟩ :=
    Subgroup.exists_large_subgroup_commutator_le_of_quotient_four B support R hRsupport
      hBS hBR hN hcardR fixed (hZsupport hfixedZ) hfixedR hfixed
  have hCmax : C ≤ nineNineCommutatorBound B support R
      (nine_nine_previous_normalizes_first_center ctx.toLocalContext hb previous hprevious) := by
    apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
    exact ⟨hCB, (Subgroup.commutator_comm C support).trans_le hCcomm⟩
  rw [nine_nine_maximal_eq_intersection ctx hb support (hsupport.trans hcore)
    hcomm previous hprevious hne] at hCmax
  have hCI := Subgroup.card_le_of_le hCmax
  have hpositive : 0 < Nat.card
      (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) :=
    Nat.card_pos
  have hCcard' : Nat.card (VAt ctx.Γ previous) ≤ 2 * Nat.card C := by
    change Nat.card (VAt ctx.Γ previous) ≤ 2 * Nat.card C at hCcard
    exact hCcard
  have hCI' : Nat.card C ≤ Nat.card
      (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) := by
    change Nat.card C ≤ Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) at hCI
    exact hCI
  have hlarge' : 4 * Nat.card
      (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous) := by
    change 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous) at hlarge
    exact hlarge
  omega

end Stellmacher.SectionNine
