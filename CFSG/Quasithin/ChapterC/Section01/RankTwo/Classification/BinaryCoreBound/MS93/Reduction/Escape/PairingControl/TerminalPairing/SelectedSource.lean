module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.SelectedSource.Backward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.SelectedIncidence

/-!
# Native incidence from the source backward Z-cover

The source deduction Z_a <= Vcirc_d Z_d, with d a moving neighbor of a,
gives a nonzero native intersection at d. Both Z_a and Z_d lie in the
radius at their common edge. If its intersection with Vcirc_d were only
U_d, the cover would put Z_a in Z_d and hence in B_d, contradicting the
proved symmetry of moving neighbors. Vertex transitivity then transports
the native incidence to the prescribed terminal predecessor.

Source: MS93 (4.3.2), final paragraph of printed p.885 and the terminal
pairing on p.886. No terminal pairing is used to obtain the backward cover.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing.SelectedSource
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
open Geometry.Selection.Centralizer.Generation

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R}

private theorem nativeIncidence_of_backward_cover
    (hb : 2 < geometry.b R) (facts : ContraryLocalFacts geometry)
    {p : Counterexample geometry} (choice : BackwardChoice p)
    (hcover : Z R p.a ≤ Vcirc R choice.back ⊔ Z R choice.back) :
    NativeIncidence choice.back := by
  have hd := moving_color p.color_a choice.moving
  have hrev := facts.moving_symmetric p.a choice.back p.color_a choice.moving
  have hstart : Z R p.a ≤ V R choice.edge :=
    le_iSup_of_le p.a (le_iSup_of_le (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr choice.adjacent_start)]
      decide) le_rfl)
  have hback : Z R choice.back ≤ V R choice.edge :=
    le_iSup_of_le choice.back (le_iSup_of_le (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr choice.adjacent_back)]
      decide) le_rfl)
  have hnorm : Z R choice.back ≤ normalizer (Vcirc R choice.back : Set (FreeAmalgam R)) :=
    (Z_le_stabilizer R choice.back).trans (Vcirc_normalized choice.back)
  refine ⟨choice.edge, choice.adjacent_back, ?_⟩
  intro hnative
  apply hrev.2
  intro x hx
  have hprod := hcover hx
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hnorm] at hprod
  obtain ⟨v, hv, z, hz, hvz⟩ := hprod
  change v * z = x at hvz
  have hvEdge : v ∈ V R choice.edge := by
    have hxEdge : v * z ∈ V R choice.edge := by
      rw [hvz]
      exact hstart hx
    have h := (V R choice.edge).mul_mem hxEdge ((V R choice.edge).inv_mem (hback hz))
    simpa only [mul_inv_cancel_right] using h
  have hvU : v ∈ U R choice.back := hnative ⟨hv, hvEdge⟩
  apply EdgeTransfer.Z_le_B hb choice.back hd
  rw [← hvz]
  exact (Z R choice.back).mul_mem (U_le_Z choice.back hvU) hz

omit [Finite M] in
private theorem nativeIncidence_transport {a d : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (incidence : NativeIncidence a) : NativeIncidence d := by
  obtain ⟨s, has, hs⟩ := incidence
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R ha
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R hd
  let k := g⁻¹ * h
  have hka : act R k a = d := by
    rw [hg, act_mVertex, mul_inv_cancel_left, ← hh]
  refine ⟨act R k s, ?_, ?_⟩
  · rw [← hka]
    exact (adjacent_act_iff R k _ _).mpr has
  · intro hle
    apply hs
    apply (map_le_map_iff_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
      (MulAut.conj k⁻¹).injective).mp
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k⁻¹).injective,
      ← Vcirc_act, ← V_act, ← U_act, hka]
    exact hle

/-- The genuine selected backward cover produces native incidence at the actual
terminal predecessor, with no remaining geometric premise. -/
theorem nativeIncidence_of_selected_source (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (seed : TerminalSeed p) (chosen : CentralizerChoice p) : NativeIncidence p.c := by
  obtain ⟨choice, _, _, _, _, _, hcover⟩ :=
    LocalProducts.SelectedSource.exists_backward_deductions source hb modules transfer
      initial facts p bad seed.six_lt chosen
  exact nativeIncidence_transport (moving_color p.color_a choice.moving) p.before_color
    (nativeIncidence_of_backward_cover hb facts choice hcover)

/-- The original unchanged geometric seed record is constructed from the
selected source data, with all flag, action and smallness fields discharged. -/
theorem nonempty_edgeSeed_of_selected_source (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (seed : TerminalSeed p) (chosen : CentralizerChoice p) :
    Nonempty (EdgeSeedAt source p.c seed.t p.before_color) :=
  Geometry.Selection.Six.EdgeSeed.nonempty_at_edge_of_incidence source hb modules
    initial facts p bad p.before_color seed.adjacent
    (nativeIncidence_of_selected_source source hb modules transfer initial facts p bad seed chosen)

/-- Apply the actual rank-one pairing to the source-selected terminal edge. -/
theorem terminal_chain_of_selected_source (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (seed : TerminalSeed p) (chosen : CentralizerChoice p) :
    ⁅Vcirc R p.a, Vcirc R p.c⁆ ≤ ⁅Z R p.a, Vcirc R p.c⁆ ∧
      ⁅Z R p.a, Vcirc R p.c⁆ ≤ Z R p.a :=
  SelectedIncidence.terminal_chain_of_native_incidence source hb modules initial facts p bad seed
    (nativeIncidence_of_selected_source source hb modules transfer initial facts p bad seed chosen)

/-- The terminal faithful-action consumer closes the selected bad branch. -/
theorem false_of_selected_source (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (seed : TerminalSeed p) (chosen : CentralizerChoice p) : False :=
  SelectedIncidence.false_of_native_incidence source hb modules initial facts p bad seed
    (nativeIncidence_of_selected_source source hb modules transfer initial facts p bad seed chosen)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing.SelectedSource
