module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.RadiusNatural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed

/-!
# A native witness from the contained six-step path

Faithfulness on Vcirc_a/U_a forces the endpoint commutator R₀ outside U_a.
The initial order-four calculation identifies R₀ with [Vcirc_a,Z_a′],
so it belongs to Vcirc_a. If R₀ lies in Z_middle, it also belongs to the
radius group at the first edge. This is an actual native intersection.
Conjugation transports its existence to any M-vertex, and local edge
transitivity constructs the prescribed seed at (c,choice.t).

These results use the contained six-step configuration, not a generic
inference from full-radius generation. They do not yet prove its contradiction.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(i)--(iii) and
(4.3.2)(5), printed pp.882--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Direct
open Centralizer.Generation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R} {p : Counterexample geometry}

theorem radius_not_le_start_natural (source : LocalSource L R)
    (hb : 2 < geometry.b R) (facts : ContraryLocalFacts geometry) :
    ¬ radiusCommutator p.a p.a' ≤ U R p.a := by
  intro h
  obtain ⟨o⟩ := facts.opposite p.a p.color_a
  let S := stabilizer R p.a
  have hC : Vcirc R p.a ≤ S := (Vcirc_le_V p.a).trans
    ((geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1))
  have hJ : Z R p.a' ≤ S := p.end_Z_le_start_stabilizer
  have hc : ⁅(Z R p.a').subgroupOf S, (Vcirc R p.a).subgroupOf S⁆ ≤
      (U R p.a).subgroupOf S := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hC, map_subgroupOf_eq_of_le hJ,
      commutator_comm]
    exact (commutator_mono (Vcirc_le_V p.a) le_rfl).trans h
  have hk := FirstPairing.Orientation.ImageCases.natural_actor_le_kernel
    o.dual.graphNatural ((Z R p.a').subgroupOf S) hc
  rw [o.kernel] at hk
  apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  intro x hx
  exact hk (show (⟨x, hJ hx⟩ : S) ∈ (Z R p.a').subgroupOf S from hx)

theorem native_at_start_of_contained (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (ip : InitialFacts p) (path : Selection.SixPath p)
    (hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle) :
    NativeIncidence p.a := by
  have hb : 2 < geometry.b R := by rw [path.six]; decide
  refine ⟨path.first, path.start_first_adjacent, ?_⟩
  intro h
  apply radius_not_le_start_natural source hb facts (p := p)
  apply le_trans (le_inf ?_ ?_) h
  · rw [Complement.radius_eq_moving_commutator source hb modules facts ip]
    exact le_normalizer_iff_commutator_le_left.mp
      (p.end_Z_le_start_stabilizer.trans (Vcirc_normalized p.a))
  · exact hcontained.trans (le_iSup_of_le path.middle (le_iSup_of_le (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
        (adjacent_symm R path.first_middle_adjacent))]
      decide) le_rfl))

theorem native_at_of_contained (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (ip : InitialFacts p) (path : Selection.SixPath p)
    (hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle)
    {d : Vertex R} (hd : color R d = false) : NativeIncidence d := by
  obtain ⟨s, has, hs⟩ := native_at_start_of_contained source modules facts ip path hcontained
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R p.color_a
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R hd
  let k := g⁻¹ * h
  have hka : act R k p.a = d := by
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

theorem edge_at_choice_of_contained (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle) :
    Nonempty (TerminalPairing.EdgeSeedAt source p.c choice.t p.before_color) := by
  obtain ⟨ip⟩ := initial p
  exact EdgeSeed.nonempty_at_choice_of_incidence source (by rw [path.six]; decide)
    modules initial facts p bad choice
    (native_at_of_contained source modules facts ip path hcontained p.before_color)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Direct
