module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Algebra

/-!
# The normalizer span and its residual commutator

The actual P-conjugates of V_(alpha-2) lie in Q_alpha by distance estimates.
Given the bound in step (6) and the source generation equality, the checked
span lemmas give local normality and [W,Z_alpha'] <= V_alpha. Critical-pair
reversal makes Z_alpha' escape Q_alpha. Normal generation in the marked
SL3(2) quotient and residual idempotence now give [W,Ltilde_alpha] <= Vcirc_alpha.

The residual normalizes Vcirc_(alpha-2) Vcirc_alpha by this bound; the edge
kernel normalizes both factors. Their local generation proves normality
inside G_alpha. The hypotheses for step (6) remain explicit here.
Source: MS93 (1993), the paragraph following (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}
variable {p : Counterexample geometry}

theorem span_le_start_kernel (choice : BackwardChoice p) (hb : 6 < geometry.b R) :
    choice.W ≤ Q R p.a := by
  apply sup_le
  · apply iSup_le
    intro g
    have hga : act R (g : FreeAmalgam R) p.a = p.a := choice.P_le_stabilizer g.property
    change (V R choice.back).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
    rw [← V_act]
    apply V_le_Q_of_distance
      (by rw [action_preserves_color]; exact moving_color p.color_a choice.moving)
    have hd := dist_act R (g : FreeAmalgam R) choice.back p.a
    rw [hga, SimpleGraph.dist_comm (u := choice.back), choice.moving.1] at hd
    omega
  · apply V_le_Q_of_distance p.color_a
    simpa using (show 2 < geometry.b R by omega)

variable [Finite M]

theorem span_residual_le (source : LocalSource L R) (choice : BackwardChoice p)
    (initial : InitialFacts p) (hb : 6 < geometry.b R)
    (hW : choice.W ≤ Q R p.c)
    (hgen : choice.P ⊔ Z R p.a' = stabilizer R p.a) :
    ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a := by
  let S := stabilizer R p.a
  let := finite_stabilizer R p.a
  let W := choice.W.subgroupOf S
  let V₀ := (V R p.a).subgroupOf S
  let J := (Z R p.a').subgroupOf S
  let π := initial.natural_section.projection
  have hWG : choice.W ≤ S := choice.W_le_stabilizer (by omega)
  have hVG : V R p.a ≤ S := initial.natural_section.local_group
  have hJG : Z R p.a' ≤ S := p.end_Z_le_start_stabilizer
  let : W.Normal := choice.W_normal initial hW hgen
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (V_normalized p.a)
  have hker : IsPGroup 2 π.ker := by
    rw [initial.natural_section.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le p.a p.color_a).comap_subtype
  have hpW : IsPGroup 2 W :=
    ((Q_isPGroup R source.two_group source.core_le p.a p.color_a).to_le
      (span_le_start_kernel choice hb)).comap_subtype
  have hJ : ¬ J ≤ π.ker := by
    intro h
    apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    intro z hz
    have hz' := h (show (⟨z, hJG hz⟩ : S) ∈ J from hz)
    rw [initial.natural_section.module_section.projection_kernel] at hz'
    exact hz'
  have hc : ⁅W, J⁆ ≤ V₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hWG, map_subgroupOf_eq_of_le hJG]
    exact (choice.commutator_end_le_radius initial hW).trans p.radius_le_start
  have h := map_mono (f := S.subtype)
    (residual_commutator_bound π initial.natural_section.module_section.projection_surjective
      hker W V₀ J hpW hJ hc)
  dsimp only [W, V₀] at h
  simpa only [map_commutator, map_subgroupOf_eq_of_le hWG,
    map_subgroupOf_eq_of_le hVG, Vcirc, Ltilde, S] using h

theorem span_residual_le_of_step_six (source : LocalSource L R)
    (choice : BackwardChoice p) (selected : CentralizerChoice p)
    (initial : InitialFacts p) (hb : 6 < geometry.b R)
    {d : Vertex R} (hd : Before p.a p.a' d 4) (hW : choice.W ≤ Q R d)
    (hgen : choice.P ⊔ Z R p.a' = stabilizer R p.a) :
    ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a :=
  span_residual_le source choice initial hb
    (choice.W_le_predecessor_kernel selected hb hd hW) hgen

/-- The relative normality uses the two incident edges, not ambient normality. -/
theorem moving_product_normal_of_residual (source : LocalSource L R)
    {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hc : ⁅V R d, Ltilde R a⁆ ≤ Vcirc R a) :
    ((Vcirc R a ⊔ Vcirc R d).subgroupOf (stabilizer R a)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hQta : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hQtd : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have hgen : Ltilde R a ⊔ Q R t = stabilizer R a := by
    apply le_antisymm (sup_le (Ltilde_le_stabilizer a) hQta)
    rw [← source.local_generation a ha]
    exact sup_le_sup_left (Q_le_adjacent_h R ht hat) _
  rw [← hgen]
  apply sup_le
  · exact normalizes_sup_of_commutator_le _ _ _
      ((Ltilde_le_stabilizer a).trans (Vcirc_normalized a))
      ((commutator_mono (Vcirc_le_V d) le_rfl).trans hc)
  · exact (le_inf (hQta.trans (Vcirc_normalized a))
      (hQtd.trans (Vcirc_normalized d))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem backward_product_normal (source : LocalSource L R)
    (choice : BackwardChoice p) (hc : ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a) :
    ((Vcirc R p.a ⊔ Vcirc R choice.back).subgroupOf (stabilizer R p.a)).Normal :=
  moving_product_normal_of_residual source p.color_a choice.adjacent_start
    choice.adjacent_back ((commutator_mono choice.back_le_W le_rfl).trans hc)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
