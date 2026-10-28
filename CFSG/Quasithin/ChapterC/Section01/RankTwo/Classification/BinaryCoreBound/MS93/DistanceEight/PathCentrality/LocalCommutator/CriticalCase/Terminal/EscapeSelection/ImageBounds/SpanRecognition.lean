module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.ImageBounds.Involutions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.Fixedness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Head
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Dual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization.Faithfulness

/-!
# Restricting a small radius involution to the actual local span

The full-radius displacement bound restricts to W/Z_c for
W = <Z_a^{G_c}>. Passing to W/(Z_c[W,Q_c]) decreases this bound again.
Both steps use the literal quotient-conjugation action inside the finite
stabilizer, and the descended involution is nonidentity because its
projection has kernel Q_c. No equality between the span and radius
radicals is used.

Binary small-involution recognition and the existing quotient lift construct
every field of the natural section of W. The all-rho hypothesis supplies
its triple bound, and the escaping displacement supplies faithfulness on
the actual span head. The final theorem discharges this premise using the
inside-B faithfulness result and contradicts the original failure of a
natural section. It supplies the involution obstruction required by the
terminal image-bounds assembly, without its independent path selector.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), immediately after (4.4.1)(3), printed p.892; the module arguments
(1.4)--(1.5), pp.842--845, and the definition of c(U), p.881.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection.ImageBounds
open Escape.Initial.Natural.Splitting Inside.Recognition
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}


/-- The same actual involution has small displacement on the span head.
Restrict in the finite stabilizer before enlarging the denominator to
Z_c[W,Q_c]; this does not use faithfulness or natural-section inheritance. -/
theorem spanHead_small_involution_of_radius (hb : 4 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hs : HasSmallRadiusInvolution c) :
    HasSmallInvolution (spanHeadAction source geometry a c hc) := by
  obtain ⟨x, hx, htwo, hsmall⟩ := hs
  let S := stabilizer R c
  let H := localSpan a c
  let N := Escape.Initial.Natural.Splitting.localZ c
  let Q₀ := localKernel c
  let π := localProjection source c hc
  let ρ := spanHeadAction source geometry a c hc
  let := finite_stabilizer R c
  let := geometry.Z_normal c
  have hπx : π x ≠ 1 := by
    intro he
    have hk : x ∈ π.ker := he
    rw [localProjection_kernel] at hk
    exact hx hk
  refine ⟨π x, hπx, by rw [← map_pow, htwo, map_one], ?_⟩
  have hmap : (zpowers x).map (ρ.comp π) = zpowers (ρ (π x)) :=
    MonoidHom.map_zpowers _ _
  rw [← hmap]
  change Nat.card (commutatorAction ((zpowers x).map
    ((headAction H N Q₀ π (localProjection_surjective source c hc)
      (localProjection_kernel source c hc)).comp π))
    (H ⧸ (Escape.radicalPreimage Q₀ H N).subgroupOf H)) ≤ 2
  rw [headAction_comp, quotientAction_displacement_card]
  have hi := relIndex_map_map_of_injective N ⁅localRadius c, zpowers x⁆ S.subtype_injective
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R c), map_commutator,
    map_subgroupOf_eq_of_le
      ((geometry.V_le_Q (by omega) c hc).trans (fun _ hy => hy.1)),
    MonoidHom.map_zpowers] at hi
  have hsmall' : N.relIndex ⁅H, zpowers x⁆ ≤ 2 := by
    have hfull : N.relIndex ⁅localRadius c, zpowers x⁆ ≤ 2 := hi.symm.trans_le hsmall
    exact (relIndex_le_of_le_right
      (commutator_mono (comap_mono (localZSpan_le_V R hd.le)) le_rfl)
      (by exact index_ne_zero_of_finite)).trans hfull
  exact (relIndex_le_of_le_left
    (show N ≤ Escape.radicalPreimage Q₀ H N from le_sup_left)
    (by exact index_ne_zero_of_finite)).trans hsmall'

/-- Recognize the actual local-span radical quotient, retaining its faithful
conjugation action as a separate geometric premise. -/
theorem span_section_of_small_radius_involution
    (hb : 4 < geometry.b R) {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (hfaithful : Function.Injective (spanHeadAction source geometry a c hc))
    (hs : HasSmallRadiusInvolution c) : HasNaturalSection R a c := by
  exact hasNaturalSection_of_spanHead_small_involution source geometry hb hc hd
    htriple hfaithful (spanHead_small_involution_of_radius hb hc hd hs)

/-- The all-rho hypothesis supplies the span's triple bound. Once its
faithfulness is proved, the original no-natural-section branch excludes
an involution with small full-radius displacement. -/
theorem no_small_radius_involution_of_span_faithful
    (hb : 4 < geometry.b R) {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hnone : ¬ HasNaturalSection R a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hfaithful : Function.Injective (spanHeadAction source geometry a c hc)) :
    ¬ HasSmallRadiusInvolution c := by
  intro hs
  apply hnone
  exact span_section_of_small_radius_involution hb hc hd
    ((commutator_mono (commutator_mono (localZSpan_le_V R hd.le) le_rfl) le_rfl).trans
      (radius_triple_le_Z_at_any_center (by omega) hc hall hc)) hfaithful hs

/-- Supply the literal displacement point required by the independent
inside-B faithfulness producer. Its nonmembership, natural-image inclusion
and triple bound all follow from the original terminal inputs. The sole
remaining premise is that producer's injectivity conclusion. -/
theorem no_small_radius_involution_of_inside_faithfulness
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (hnone : ¬ HasNaturalSection R a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hfaithfulness : ∀ x : stabilizer R c,
      (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆ →
      (x : FreeAmalgam R) ∉ fixedCore R c →
      (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c →
      ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c) →
      ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c →
      Function.Injective (spanHeadAction source geometry a c hc)) :
    ¬ HasSmallRadiusInvolution c := by
  have hB := hall a (by rwa [SimpleGraph.dist_comm])
  obtain ⟨x, hx, hnot, _⟩ := Inside.exists_displacement_point common ha hc hd hB hn
  have hnatural := Inside.displacement_le_Z_join_fixedCore common hb ha hc hd hB hx
  have htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c :=
    (commutator_mono (commutator_mono (localZSpan_le_V R hd.le) le_rfl) le_rfl).trans
      (radius_triple_le_Z_at_any_center (by omega) hc hall hc)
  exact no_small_radius_involution_of_span_faithful hb hc hd hnone hall
    (hfaithfulness x hx hnot hnatural hB htriple)

/-- The terminal source inputs exclude a small full-radius involution.
Its restriction yields the complete natural section of the actual local
span, contrary to the nonnatural branch. The backward witness is retained
to match the image-bounds consumer; this module obstruction does not need
its path or any further selection hypothesis. -/
theorem no_small_radius_involution
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (hnone : ¬ HasNaturalSection R a c)
    (_w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ¬ HasSmallRadiusInvolution c := by
  apply no_small_radius_involution_of_inside_faithfulness common hb ha hc hd hn hnone hall
  intro x hx hxD _ _ htriple
  exact spanHeadAction_injective_of_escaping source geometry hb ha hc hd x hx hxD htriple

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection.ImageBounds
