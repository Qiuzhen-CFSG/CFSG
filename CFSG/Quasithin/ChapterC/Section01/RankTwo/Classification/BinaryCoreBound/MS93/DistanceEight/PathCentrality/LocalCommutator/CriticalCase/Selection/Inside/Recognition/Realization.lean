module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization.Transport

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization.PointData

/-!
# Assembling the local escaping configuration from the marked point

Given the identification of the literal relative normalizer of xD_c with
the preimage of its natural point stabilizer, the actual K-span constructs
every field of EscapingConfiguration. A critical endpoint supplies an
involution; its cyclic subgroup and escaping action span lie in the actual
endpoint image and source escaping span. Monotonicity transfers the supplied
small commutator bound.

The marking identification and faithfulness of the local head are still
independent obligations. No natural-section recognition is used here.
Source: MS93 (1.6), pp.845–847, and (4.4.1)(2), printed p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem projected_mem_conjugate (source : LocalSource L R)
    {c : Vertex R} (hc : color R c = false) (x : stabilizer R c) (K : Subgroup SL)
    (hK : ∀ g : stabilizer R c, (g : FreeAmalgam R) ∈ pointNormalizer c x ↔
      localProjection source c hc g ∈ K)
    (g z : stabilizer R c)
    (hz : (z : FreeAmalgam R) ∈ NormalizerTransfer.rightConjugate (pointNormalizer c x) g) :
    localProjection source c hc z ∈
      NormalizerTransfer.rightConjugate K (localProjection source c hc g) := by
  obtain ⟨k, hk, he⟩ := hz
  let kS : stabilizer R c := ⟨k, hk.1⟩
  refine ⟨localProjection source c hc kS, (hK kS).mp hk, ?_⟩
  have h : g⁻¹ * kS * g = z := by
    apply Subtype.ext
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, coe_mul, coe_inv] using he
  change MulAut.conj (localProjection source c hc g)⁻¹ (localProjection source c hc kS) =
    localProjection source c hc z
  rw [MulAut.conj_apply, inv_inv]
  have hh := congrArg (localProjection source c hc) h
  simpa only [map_mul, map_inv] using hh

/-- Escaping a single projected involution implies the source endpoint escape
condition. No assertion about the order of the entire endpoint image is needed. -/
theorem actionEscapingSpan_le_spanHeadImage (source : LocalSource L R)
    (geometry : Geometry R) {a c e : Vertex R} (hc : color R c = false)
    (x : stabilizer R c) (K : Subgroup SL)
    (hK : ∀ g : stabilizer R c, (g : FreeAmalgam R) ∈ pointNormalizer c x ↔
      localProjection source c hc g ∈ K)
    (t : SL) (ht : t ∈ ((Z R e).subgroupOf (stabilizer R c)).map
      (localProjection source c hc)) :
    actionEscapingSpan (spanHeadAction source geometry a c hc) K t
      (spanHeadImage geometry a c (normalizerSpan a c x)) ≤
    spanHeadImage geometry a c (escapingSpan a c e x) := by
  apply iSup_le
  intro s
  obtain ⟨g, rfl⟩ := localProjection_surjective source c hc s
  apply iSup_le
  intro hescape
  rw [spanHeadImage_conjugate]
  apply spanHeadImage_mono
  apply le_iSup_of_le g
  apply le_iSup_of_le (show ¬ Z R e ≤
    NormalizerTransfer.rightConjugate (pointNormalizer c x) g from ?_)
  · exact le_rfl
  · intro hall
    obtain ⟨z, hz, rfl⟩ := ht
    exact hescape (projected_mem_conjugate source hc x K hK g z (hall hz))

/-- Once the actual quotient point is marked, all remaining configuration
fields are proved on the literal local-span head. -/
theorem escapingConfiguration_of_pointNormalizer (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c e : Vertex R}
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (x : stabilizer R c)
    (marking : SL ≃* SL) (v : Fin 3 → ZMod 2) (hv : v ≠ 0)
    (hK : ∀ g : stabilizer R c, (g : FreeAmalgam R) ∈ pointNormalizer c x ↔
      localProjection source c hc g ∈ markedPointStabilizer marking v)
    (hsmall : (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2) :
    ∃ d : EscapingConfiguration (spanHeadAction source geometry a c hc),
      d.marking = marking ∧ d.point = v ∧
      d.seed = spanHeadImage geometry a c (normalizerSpan a c x) ∧
      d.involution ∈ ((Z R e).subgroupOf (stabilizer R c)).map
        (localProjection source c hc) := by
  obtain ⟨t, ht, hsq, hmem⟩ := exists_endpoint_involution source geometry common (by omega) hc p
  let d : EscapingConfiguration (spanHeadAction source geometry a c hc) := {
    marking := marking
    point := v
    point_ne_zero := hv
    involution := t
    involution_ne_one := ht
    involution_sq := hsq
    seed := spanHeadImage geometry a c (normalizerSpan a c x)
    invariant := by
      intro s hs
      obtain ⟨g, rfl⟩ := localProjection_surjective source c hc s
      exact spanHead_normalizerSpan_invariant source geometry a c hc x g ((hK g).mpr hs)
    generates := spanHead_normalizerSpan_generates source geometry (by omega) hc hd.le x
    small := by
      have hle := actionDisplacement_mono_both (spanHeadAction source geometry a c hc)
        (zpowers_le.mpr hmem)
        (actionEscapingSpan_le_spanHeadImage source geometry hc x _ hK t hmem)
      exact (card_le_of_le hle).trans
        (escaping_actionDisplacement_card_le_two source geometry hb hc hd p x hsmall) }
  exact ⟨d, rfl, rfl, rfl, hmem⟩

/-- Consumer of the marking of xD_c. The seed and endpoint used above are
unchanged; existence of the marking remains the separate point construction. -/
theorem escapingConfiguration_nonempty_of_markedPoint (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c e : Vertex R}
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (x : stabilizer R c)
    (point : LocalPointMarking source c hc x)
    (hsmall : (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2) :
    Nonempty (EscapingConfiguration (spanHeadAction source geometry a c hc)) := by
  obtain ⟨d, _⟩ := escapingConfiguration_of_pointNormalizer source geometry common hb hc hd p x
    point.naturalU.marking (point.naturalU.coordinates point.lift).toAdd
    point.nonzero point.normalizer hsmall
  exact ⟨d⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
